---
layout: post
title: Under the Hood - Implementing system_clock and steady_clock
date: 2024-08-21 00:32:14
categories:
  - [Computer Science, Programming Language, C++]
---

Time measurement and interval calculation are crucial components in various software systems, particularly for metrics, tracing, and logging. As these operations are frequently performed, there's a legitimate concern about their potential impact on program performance. To address this concern and gain a deeper understanding of time-related functions, this blog post delves into the implementation details of `system_clock` and `steady_clock`. By exploring their underlying mechanisms, we aim to shed light on the efficiency of these time-keeping tools and alleviate worries about performance overhead.

## Unveiling the Implementation of `system_clock`

The key point to understand is that `system_clock` operates with zero syscalls. As noted in [Stack Overflow: How does one do a "zero-syscall clock_gettime" without dynamic linking?](https://stackoverflow.com/questions/71848553/how-does-one-do-a-zero-syscall-clock-gettime-without-dynamic-linking):

> Call into the `clock_gettime` implementation in the VDSO, to use code+data exported by the kernel.

According to [Wikipedia: vDSO](https://en.wikipedia.org/wiki/VDSO):

> vDSO (virtual dynamic shared object) is a kernel mechanism for exporting a carefully selected set of kernel space routines to user space applications so that applications can call these kernel space routines in-process, **without incurring the performance penalty of a mode switch from user mode to kernel mode** that is inherent when calling these same kernel space routines by means of the system call interface.

In the vDSO, `clock_gettime` uses the `RDTSC` instruction to obtain the time, as explained on [Stack Exchange: Should I be seeing (non-VDSO) clock_gettime() syscalls on x86_64 using HPET?](https://unix.stackexchange.com/questions/553845/should-i-be-seeing-non-vdso-clock-gettime-syscalls-on-x86-64-using-hpet):

> In the vDSO, `clock_gettimeofday` and related functions are reliant on specific clock modes; see `__arch_get_hw_counter`. If the clock mode is `VCLOCK_TSC`, the time is read without a syscall, using `RDTSC`; if it's `VCLOCK_PVCLOCK` or `VCLOCK_HVCLOCK`, it's read from a specific page to retrieve the information from the hypervisor.

To check the clock mode, [AWS re:Post: How do I manage the clock source for EC2 instances running Linux?](https://repost.aws/knowledge-center/manage-ec2-linux-clock-source) suggests:

> To find the currently set clock source, list the contents of the current_clocksource file:
>
> `cat /sys/devices/system/clocksource/clocksource0/current_clocksource`

In my virtual machine, it shows `tsc`.

[Félix Cloutier: RDTSC](https://www.felixcloutier.com/x86/rdtsc) describes `RDTSC`:

> The processor monotonically increments the time-stamp counter `MSR` every clock cycle and resets it to 0 whenever the processor is reset. See "Time Stamp Counter" in Chapter 18 of the Intel@64 and IA-32 Architectures Software Developer's Manual, Volume 3B, for specific details of the time stamp counter behavior.

Let's trace the `system_clock::now` function from GCC to Linux:

1. [`system_clock::now`](https://github.com/gcc-mirror/gcc/blob/723b30bee4e4fa3feba9ef03ce7dca95501e1555/libstdc%2B%2B-v3/src/c%2B%2B11/chrono.cc#L59) calls [`__vdso_clock_gettime`](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/arch/x86/entry/vdso/vclock_gettime.c#L38).
2. `__vdso_clock_gettime` calls [`__cvdso_clock_gettime_common`](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/lib/vdso/gettimeofday.c#L268).
3. `__cvdso_clock_gettime_common` calls [`do_hres`](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/lib/vdso/gettimeofday.c#L164).
4. `do_hres` calls [`__arch_get_hw_counter`](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/arch/x86/include/asm/vdso/gettimeofday.h#L254)
5. Finally, `__arch_get_hw_counter` calls `rdtsc_ordered`.

## `system_clock` vs. `steady_clock`: Key Differences

The key difference between system_clock and steady_clock lies in their base times: [`system_clock::now`](https://github.com/gcc-mirror/gcc/blob/723b30bee4e4fa3feba9ef03ce7dca95501e1555/libstdc%2B%2B-v3/src/c%2B%2B11/chrono.cc#L59) uses `CLOCK_REALTIME` with `clock_gettime`, [`steady_clock::now`](https://github.com/gcc-mirror/gcc/blob/723b30bee4e4fa3feba9ef03ce7dca95501e1555/libstdc%2B%2B-v3/src/c%2B%2B11/chrono.cc#L87) uses `CLOCK_MONOTONIC`. In the vDSO, [do_hres](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/lib/vdso/gettimeofday.c#L133) uses `CLOCK_REALTIME` and `CLOCK_MONOTONIC` as indices for `vd->basetime` to retrieve different base timestamps. I suspect that different indices of `vd->basetime` provide different base times. However, since `__arch_get_vdso_data` is a kernel function, I can't call it directly to test this.

## Efficiency Comparison: `CLOCK_THREAD_CPUTIME_ID` vs. `system_clock`

In the implementation of [`__cvdso_clock_gettime_common`](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/lib/vdso/gettimeofday.c#L259-L266), when [`CLOCK_THREAD_CPUTIME_ID`](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/include/uapi/linux/time.h#L52) is used, it doesn't match any of the masks [`VDSO_HRES`](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/include/vdso/datapage.h#L29), `VDSO_COARSE`, or `VDSO_RAW`. As a result, the function returns -1. This return value triggers the caller function [`__cvdso_clock_gettime_data`](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/lib/vdso/gettimeofday.c#L278) to fallback to [`clock_gettime_fallback`](https://github.com/torvalds/linux/blob/6e4436539ae182dc86d57d13849862bcafaa4709/arch/x86/include/asm/vdso/gettimeofday.h#L116), leading to a syscall. Retrieving thread CPU time using `CLOCK_THREAD_CPUTIME_ID` is slower than using `system_clock::now` because it requires a syscall.

## Benchmark

```cpp
#include <chrono>
#include <ctime>
#include <iostream>
int main() {
  auto begin = std::chrono::system_clock::now();
  for (auto i = 0; i < 1000000; i++) {
    std::chrono::system_clock::now();
  }
  auto end = std::chrono::system_clock::now();
  std::cout << std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() << std::endl;
  //
  begin = std::chrono::system_clock::now();
  for (auto i = 0; i < 1000000; i++) {
    std::chrono::steady_clock::now();
  }
  end = std::chrono::system_clock::now();
  std::cout << std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() << std::endl;
  //
  begin = std::chrono::system_clock::now();
  for (auto i = 0; i < 1000000; i++) {
    timespec t;
    clock_gettime(CLOCK_THREAD_CPUTIME_ID, &t);
  }
  end = std::chrono::system_clock::now();
  std::cout << std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count() << std::endl;
  return 0;
}
```

```bash
# g++ test.cc -O0 -o test
# ./test
24975888
23460648
581884166
```

The benchmark results support the analysis:

+ `system_clock` and `steady_clock` have similar performance, while `CLOCK_THREAD_CPUTIME_ID` is significantly slower due to the syscall fallback.
+ Calling `system_clock::now` costs 25 nanoseconds, demonstrating its high efficiency.
