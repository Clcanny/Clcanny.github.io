---
layout: post
title: Perf JNI Program
date: 2021-11-26 19:57:49
categories:
  - [Computer Science, Performance Analysis]
---

# 如何确认 OpenJDK 的版本号？

用 [arthas dashboard](https://arthas.aliyun.com/doc/en/dashboard.html) 命令可以查看运行进程的 Java 位置：

```bash
# java -jar arthas-boot.jar 156
# dashboard
java.home /usr/lib/jvm/java-8-oracle/jre
```

再用 `java -version` 命令来查看版本号：
```bash
# /usr/lib/jvm/java-8-oracle/jre/bin/java -version
java version "1.8.0_40"
Java(TM) SE Runtime Environment (build 1.8.0_40-b25)
Java HotSpot(TM) 64-Bit Server VM (build 25.40-b25, mixed mode)
```

笔者工作中用到的 OpenJDK build 是 1.8.0\_131-b11 ，下文都会使用这个版本的 OpenJDK 。

# 如何下载 OpenJDK 的源代码？

OpenJDK 的源代码可以从以下网址找：

+ [GitHub: openjdk/jdk](https://github.com/openjdk/jdk)
+ [GitHub: openjdk/jdk8u](https://github.com/openjdk/jdk8u)
+ [OpenJDK projects](https://hg.openjdk.java.net/)
+ [OpenJDK projects: jdk8u/jdk8u/tags](https://hg.openjdk.java.net/jdk8u/jdk8u/tags)

笔者目前工作中用到的 JDK 是 jdk1.8.0\_131-b11 ，最接近的版本是：

+ [GitHub: openjdk/jdk8u jdk8u131-b11](https://github.com/openjdk/jdk8u/tree/jdk8u131-b11)
+ [OpenJDK projects: changeset 1915:94b119876028, Added tag jdk8u131-b10 for changeset 725620ca52fb](https://hg.openjdk.java.net/jdk8u/jdk8u/rev/94b119876028)

```bash
git clone https://github.com/openjdk/jdk8u.git
git checkout jdk8u131-b11
```

# 如何编译 OpenJDK ？

+ perf 需要符号表才能正确插入 uprobe ，所以编译 OpenJDK 时需要顺带编译符号表。有关符号的编译选项可以参考：
  + [腾讯云：Centos 编译 JDK8 源码](https://cloud.tencent.com/developer/article/1701909)
  + [OpenJDK building.md: Configure Arguments for Tailoring the Build](https://github.com/openjdk/jdk/blob/master/doc/building.md#configure-arguments-for-tailoring-the-build)
  + [OpenJDK building.md: Native Debug Symbols](https://github.com/openjdk/jdk/blob/master/doc/building.md#native-debug-symbols)
+ 根据 [Stack Overflow: Scrambled arguments when building OpenJDK](https://stackoverflow.com/questions/21246042/scrambled-arguments-when-building-openjdk) 和 [JDK BUG SYSTEM: adjust-mflags.sh failed build with GNU Make 4.0 with -I\<path contains j\>](https://bugs.openjdk.java.net/browse/JDK-8028407) 的说法，`make` 不能使用 4.0 及以上版本，否则会报错：

```bash
/usr/bin/make: invalid option -- '8'
/usr/bin/make: invalid option -- 'u'
/usr/bin/make: invalid option -- '/'
/usr/bin/make: invalid option -- 'a'
/usr/bin/make: invalid option -- '/'
/usr/bin/make: invalid option -- 'c'
```

```dockerfile
# build_openjdk.dockerfile
FROM debian:jessie
LABEL maintainer="837940593@qq.com"

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update

RUN apt-get install -y cpio file build-essential make zip unzip
RUN apt-get install -y libX11-dev libxext-dev libxrender-dev libxtst-dev libxt-dev
RUN apt-get install -y libcups2-dev
RUN apt-get install -y libfreetype6-dev
RUN apt-get install -y libasound2-dev
RUN apt-get install -y libfontconfig1-dev
# Install boot jdk.
RUN apt-get install -y openjdk-7-jdk

# Downgrade make to 3.82.
WORKDIR /tmp
RUN apt-get install -y wget
RUN wget https://ftp.gnu.org/gnu/make/make-3.82.tar.gz --no-check-certificate
RUN tar -xzvf make-3.82.tar.gz
WORKDIR /tmp/make-3.82
RUN ./configure --prefix=/usr
RUN make && make install
RUN make --version

RUN apt-get install -y git
RUN git clone https://github.com/openjdk/jdk8u.git /jdk8u
WORKDIR /jdk8u
RUN git checkout -b jdk8u131-b11
# https://stackoverflow.com/questions/52377684/compile-jdk8-error-could-not-find-freetype
ENV DISABLE_HOTSPOT_OS_VERSION_CHECK ok
RUN bash configure --with-freetype-include=/usr/include/freetype2 \
                   --with-freetype-lib=/usr/lib/x86_64-linux-gnu  \
                   --with-debug-level=slowdebug                   \
                   --enable-debug-symbols
RUN make JOBS=8 all
RUN tar -czvf linux-x86_64-normal-server-slowdebug-jdk8u131-b11.tar.gz build
```

```bash
# docker build -t build_openjdk:jdk8u131-b11 -f build_openjdk.dockerfile .
# docker cp $(docker create --rm build_openjdk:jdk8u131-b11):/jdk8u/linux-x86_64-normal-server-slowdebug-jdk8u131-b11.tar.gz .
```

# 用 perf-map-agent 提供 Java 调用栈

JIT 会动态地将热点代码编译成 native code ，这会导致 perf 没有这部分代码的符号表，从而不认识相关函数。[perf-map-agent](https://github.com/jvm-profiling-tools/perf-map-agent) 就是为了解决这个问题而诞生的。

> Linux `perf` tools will expect symbols for code executed from unknown memory regions at `/tmp/perf-<pid>.map`. This allows runtimes that generate code on the fly to supply dynamic symbol mappings to be used with the `perf` suite of tools.
> perf-map-agent is an agent that will generate such a mapping file for Java applications. It consists of a Java agent written C and a small Java bootstrap application which attaches the agent to a running Java process.

```dockerfile
# build_perf_map_agent.dockerfile
FROM build_openjdk:jdk8u131-b11
RUN apt-get install -y cmake

RUN git clone https://github.com/jvm-profiling-tools/perf-map-agent.git /perf-map-agent
WORKDIR /perf-map-agent
ENV JAVA_HOME /jdk8u/build/linux-x86_64-normal-server-release/jdk
RUN cmake .
RUN make
RUN tar -czvf perf-map-agent-jdk8u131-b11.tar.gz \
              bin                                \
              out/attach-main.jar                \
              out/libperfmap.so
```

```bash
# docker build -t build_perf_map_agent:jdk8u131-b11 -f build_perf_map_agent.dockerfile .
# docker cp $(docker create --rm build_perf_map_agent:jdk8u131-b11):/perf-map-agent/perf-map-agent-jdk8u131-b11.tar.gz .
```

# 一个简单的例子

```java
// HelloWorld.java
public class HelloWorld {
  public void sleep() {
    sleepInSynchronizedArea();
  }

  private synchronized void sleepInSynchronizedArea() {
    try {
      Thread.sleep(1000);
    } catch (InterruptedException e) {
    }
  }

  public void sayHelloWorld() {
    sayHelloWorldInSynchronizedArea();
  }

  private synchronized void sayHelloWorldInSynchronizedArea() {
    System.out.println("Hello, world!");
  }
}
```

```cpp
// main.cpp
#include <jni.h>
#include <pthread.h>

#include <cassert>
#include <chrono>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <thread>

void print_time() {
  using std::chrono::duration_cast;
  using std::chrono::milliseconds;
  using std::chrono::system_clock;
  std::cout << duration_cast<milliseconds>(
                 system_clock::now().time_since_epoch())
                 .count()
            << std::endl;
}

void say_hello(JNIEnv* env, jobject obj, jmethodID mid) {
  env->CallVoidMethod(obj, mid);
}

int main() {
  JNIEnv* env = nullptr;
  JavaVM* jvm = nullptr;

  JavaVMOption options[4];
  options[0].optionString = "-Djava.class.path=.";
  options[1].optionString = "-XX:+UnlockDiagnosticVMOptions";
  options[2].optionString = "-XX:+PreserveFramePointer";
  options[3].optionString = "-XX:+ShowHiddenFrames";
  JavaVMInitArgs vm_args;
  std::memset(&vm_args, 0, sizeof(vm_args));
  vm_args.version = JNI_VERSION_1_2;
  vm_args.nOptions = 1;
  vm_args.options = options;

  assert(JNI_CreateJavaVM(&jvm, reinterpret_cast<void**>(&env), &vm_args) !=
         JNI_ERR);
  assert(env != nullptr);

  jclass cls = env->FindClass("HelloWorld");
  assert(cls != 0);
  jobject obj = env->AllocObject(cls);
  jmethodID sleep_mid = env->GetMethodID(cls, "sleep", "()V");
  assert(sleep_mid != 0);
  jmethodID say_hello_mid = env->GetMethodID(cls, "sayHelloWorld", "()V");
  assert(say_hello_mid != 0);

  std::thread sleep_thread([jvm, obj, sleep_mid]() {
    pthread_setname_np(pthread_self(), "sleep-thread");
    JNIEnv* env = nullptr;
    jvm->AttachCurrentThread(reinterpret_cast<void**>(&env), nullptr);
    assert(env != nullptr);
    while (true) {
      env->CallVoidMethod(obj, sleep_mid);
      std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
  });
  std::thread say_hello_thread([jvm, obj, say_hello_mid]() {
    pthread_setname_np(pthread_self(), "sh-thread");
    JNIEnv* env = nullptr;
    jvm->AttachCurrentThread(reinterpret_cast<void**>(&env), nullptr);
    assert(env != nullptr);
    while (true) {
      print_time();
      say_hello(env, obj, say_hello_mid);
      print_time();
      std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
  });
  sleep_thread.join();
  say_hello_thread.join();
}
```

```bash
./build/linux-x86_64-normal-server-slowdebug/jdk/bin/javac HelloWorld.java
g++ -std=c++11 -O0 -ggdb main.cpp                                              \
  -I./build/linux-x86_64-normal-server-slowdebug/jdk/include                   \
  -I./build/linux-x86_64-normal-server-slowdebug/jdk/include/linux             \
  -L./build/linux-x86_64-normal-server-slowdebug/jdk/lib/amd64/server          \
  -Wl,-rpath=./build/linux-x86_64-normal-server-slowdebug/jdk/lib/amd64/server \
  -ljvm -lpthread -lunwind                                                     \
  -o main
```

# 分析

## 插入 uprobe

perf probe 的命令格式可以参考 [perf-probe(1) — Linux manual page](https://man7.org/linux/man-pages/man1/perf-probe.1.html) ，值得注意的是：

> PROBE SYNTAX
> Probe points are defined by following syntax.
> 1) Define event based on function name
>    [[GROUP:]EVENT=]FUNC[@SRC][:RLN|+OFFS|%return|;PTN] [ARG ...]

以函数 `say_hello` 的 return probe 为例：

```bash
        exit_say_hello=_Z9say_helloP7JNIEnv_P8_jobjectP10_jmethodID%return
[GROUP:]EVENT         =FUNC                                        %return
```

```bash
# whoami
root
# readelf --wide --symbols main | grep say_hello
113: 0000000000001850 7 FUNC GLOBAL DEFAULT 14 _Z9say_helloP7JNIEnv_P8_jobjectP10_jmethodID
# perf probe -x main --add entry_say_hello=_Z9say_helloP7JNIEnv_P8_jobjectP10_jmethodID
# perf probe -x main --add exit_say_hello=_Z9say_helloP7JNIEnv_P8_jobjectP10_jmethodID%return
# cat /sys/kernel/debug/tracing/uprobe_events
p:probe_main/enter_say_hello /home/demons/build/main:0x000000000000122d
r:probe_main/exit_say_hello /home/demons/build/main:0x000000000000122d
# perf list | grep probe_main
probe_main:entry_say_hello                         [Tracepoint event]
probe_main:exit_say_hello                          [Tracepoint event]
```

## 跟踪 `say_hello` 函数耗时

```bash
# perf record
Usage: perf record [<options>] [<command>]
   or: perf record [<options>] -- <command> [<options>]
   -R, --raw-samples     collect raw sample records from all opened counters
```

```bash
# perf record -e probe_main:entry_say_hello -e probe_main:exit_say_hello -R -p 3429
[ perf record: Woken up 1 times to write data ]
[ perf record: Captured and wrote 0.090 MB perf.data (15 samples) ]
# perf script | head -n 4
main  3449 [004] 22430.470425: probe_main:entry_say_hello: (556a3249122d)
main  3449 [004] 22431.470482:  probe_main:exit_say_hello: (556a3249122d <- 556a3249137f)
main  3449 [004] 22431.570604: probe_main:entry_say_hello: (556a3249122d)
main  3449 [004] 22432.570643:  probe_main:exit_say_hello: (556a3249122d <- 556a3249137f)
```

根据 [Stack Overflow: What is meaning of timestamp in perf?](https://stackoverflow.com/questions/61425982/what-is-meaning-of-timestamp-in-perf) 的说法：

> Timestamps "X.Y" in perf output are X seconds and Y microseconds. In `perf script` output it probably X seconds since linux boot. Similar time format is used in `dmesg` output.

我们发现每次执行 `say_hello` 函数都需要 1s+ 。那为什么一个这么简单的函数会耗时这么久？

## 分析 `say_hello` 函数是 CPU 密集型还是 IO 密集型

当前线程出让 CPU 时会触发 `sched:sched_switch` 事件，当前线程获得 CPU 时会触发 `sched:sched_wakeup` 事件，我们可以利用这两个事件判断线程究竟是在等锁（ IO ）还是在执行耗 CPU 的代码。

根据 [Basic Usage (with examples) for each of the Yocto Tracing Tools: Filtering](https://docs.yoctoproject.org/profile-manual/usage.html#filtering) 的介绍，perf event 支持过滤器，过滤掉我们不关心的事件。`sched:sched_switch` 支持 `--filter '(prev_pid >= xxx && prev_pid <= xxx) || (next_pid >= xxx && next_pid <= xxx)'` ，`sched:sched_wakeup` 支持 `--filter '(pid <= xxx && pid >= xxx)'` ，在目标进程拥有多个线程的情况下，这两个 filter 能过滤掉大量无关事件。需要说明的是 filter 中的 `pid` 是 thread id 。

```bash
# ps aux | grep main | awk '{print $2}'
4340
# ps -eT | grep 4340
4340  4359 pts/0    00:00:00 sleep-thread
4340  4360 pts/0    00:00:01 sh-thread
```

```bash
perf record                                                             \
  -e probe_main:entry_say_hello -e probe_main:exit_say_hello            \
  -e sched:sched_switch --filter 'prev_pid == 5292 || next_pid == 5292' \
  -e sched:sched_wakeup --filter 'pid == 5292'                          \
  -R -p 5272
```

```text
   sh-thread  5292 [005] 39159.217868: probe_main:entry_say_hello: (55e0d310d2ed)
   sh-thread  5292 [005] 39159.217919: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

     swapper     0 [005] 39159.218968: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39159.218977: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

     swapper     0 [005] 39159.227033: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39159.227041: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

     swapper     0 [005] 39159.291101: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39159.291113: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

     swapper     0 [005] 39159.803180: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39159.803206: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

sleep-thread  5291 [003] 39160.217827: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
sleep-thread  5291 [003] 39160.217831: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39160.217958: probe_main:exit_say_hello: (55e0d310d2ed <- 55e0d310d467)
```

从 perf 的结果看，线程 `sh-thread` 每次获得 CPU 时间片（发生 `sched:sched_wakeup` 事件）之后，都会在 10 微秒后切走（发生 `sched:sched_switch` 事件）。而下次线程 `sh-thread` 获得时间片要在几毫秒 ~ 几百毫秒之后。因此，这是一个 IO 密集型函数。

## 线程 `sh-thread` 在等谁？

通过 `--call-graph dwarf,50` 查看线程切出时的线程栈。

```bash
perf record --call-graph dwarf,16384                                    \
  -e probe_main:entry_say_hello -e probe_main:exit_say_hello            \
  -e sched:sched_switch --filter 'prev_pid == 5292 || next_pid == 5292' \
  -e sched:sched_wakeup --filter 'pid == 5292'                          \
  -R -p 5272
```

```text
sh-thread  5292 [005] 40621.348364: probe_main:entry_say_hello: (55e0d310d2ed)
                    12ed say_hello+0xffff543e59de8000 (/home/demons/build/main)
                    1466 main::{lambda()#2}::operator()+0xffff543e59de808e (/home/demons/build/main)
        ffffffffffffffff [unknown] ([unknown])

sh-thread  5292 [005] 40621.348390:         sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]
            7fff8b81f537 __schedule+0x800074e022a7 ([kernel.kallsyms])
            7fff8b81f537 __schedule+0x800074e022a7 ([kernel.kallsyms])
            7fff8b2ee154 hrtimer_start_range_ns+0x800074e02194 ([kernel.kallsyms])
            7fff8b81f9b2 schedule+0x800074e02032 ([kernel.kallsyms])
            7fff8b2fdae1 futex_wait_queue_me+0x800074e020c1 ([kernel.kallsyms])
            7fff8b2fe816 futex_wait+0x800074e020f6 ([kernel.kallsyms])
            7fff8b2ed940 hrtimer_wakeup+0x800074e02000 ([kernel.kallsyms])
            7fff8b300a0f do_futex+0x800074e0214f ([kernel.kallsyms])
            7fff8b3ec93b kmem_cache_alloc_trace+0x800074e0211b ([kernel.kallsyms])
            7fff8b40be85 __check_object_size+0x800074e02105 ([kernel.kallsyms])
            7fff8b25fe9c arch_uretprobe_hijack_return_addr+0x800074e020ec ([kernel.kallsyms])
            7fff8b25fc4f arch_uprobe_post_xol+0x800074e0205f ([kernel.kallsyms])
            7fff8b289bc7 recalc_sigpending+0x800074e02017 ([kernel.kallsyms])
            7fff8b381d99 uprobe_notify_resume+0x800074e020c9 ([kernel.kallsyms])
            7fff8b3014df sys_futex+0x800074e0207f ([kernel.kallsyms])
            7fff8b205b7d do_syscall_64+0x800074e0208d ([kernel.kallsyms])
            7fff8b82438e entry_SYSCALL_64_after_swapgs+0x800074e02058 ([kernel.kallsyms])
                    d528 pthread_cond_timedwait@@GLIBC_2.3.2+0xffff00840a0b0128 (/lib/x86_64-linux-gnu/libpthread-2.24.so)
        ffffffffffffffff [unknown] ([unknown])

// ...

sleep-thread  5291 [002] 40622.348349:         sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
            7fff8b2a74ef ttwu_do_wakeup+0x800074e020bf ([kernel.kallsyms])
            7fff8b2a74ef ttwu_do_wakeup+0x800074e020bf ([kernel.kallsyms])
            7fff8b2a818a try_to_wake_up+0x800074e0218a ([kernel.kallsyms])
            7fff8b2a841f wake_up_q+0x800074e0203f ([kernel.kallsyms])
            7fff8b30116d do_futex+0x800074e028ad ([kernel.kallsyms])
            7fff8b3014df sys_futex+0x800074e0207f ([kernel.kallsyms])
            7fff8b205b7d do_syscall_64+0x800074e0208d ([kernel.kallsyms])
            7fff8b82438e entry_SYSCALL_64_after_swapgs+0x800074e02058 ([kernel.kallsyms])
                    d845 pthread_cond_signal@@GLIBC_2.3.2+0xffff00840a0b0065 (/lib/x86_64-linux-gnu/libpthread-2.24.so)
                  9678c8 os::PlatformEvent::unpark+0xffff008409c76068 (/home/demons/build/build/linux-x86_64-normal-server-release/jdk/lib/amd64/server/libjvm.so)

sh-thread  5292 [005] 40622.348448:  probe_main:exit_say_hello: (55e0d310d2ed <- 55e0d310d467)
                    1467 main::{lambda()#2}::operator()+0xffff543e59de808f (/home/demons/build/main)
        ffffffffffffffff [unknown] ([unknown])
```

怎么分析谁在持锁呢？

+ 看 `sys_futex` 被谁持有；
+ 看 `os::PlatformEvent::unpark` 更深的线程栈。

```bash
# export JAVA_HOME=$PWD/build/linux-x86_64-normal-server-slowdebug/jdk
./bin/create-java-perf-map.sh 5272
```

```bash
# perf script --max-stack 256
```

## 查看线程栈：JVM 部分

JVM 在执行 JIT 时会开启类似于 GCC 对栈指针的优化，导致无法 perf 无法溯源线程栈。那么 JVM 有类似于 `-fno-omit-frame-pointer` 的选项吗？

> For many years the gcc compiler has reused the frame pointer as a compiler optimization, breaking stack traces. Some applications compile with the gcc option -fno-omit-frame-pointer, to preserve this type of stack walking, however, the JVM had no equivalent option.

Brendan 向 OpenJDK 团队提交了新增了选项 `-XX:+PreserveFramePointer` 的 patch ，这个选项会告诉 JIT 不要把栈指针给优化掉。完整的故事请阅读以下文章：

+ [Stack Overflow: Printing backtraces when debugging java](https://stackoverflow.com/questions/54365079/printing-backtraces-when-debugging-java)
+ [Stack Overflow: How does linux's perf utility understand stack traces?](https://stackoverflow.com/questions/38277463/how-does-linuxs-perf-utility-understand-stack-traces)
+ [Netflix Technology Blog: Java in Flames](https://netflixtechblog.com/java-in-flames-e763b3d32166)
+ [Brendan Gregg's Blog: Linux Profiling at Netflix](https://www.brendangregg.com/blog/2015-02-27/linux-profiling-at-netflix.html)

### 用 GDB 验证 `-XX:+PreserveFramePointer` 的效果

稍稍修改 HelloWorld.java 让 `sleepInSynchronizedArea` 停留更久一些：

```java
// HelloWorld.java
public class HelloWorld {
  public void sleep() {
    sleepInSynchronizedArea();
  }

  private synchronized void sleepInSynchronizedArea() {
    try {
      Thread.sleep(1 * 60 * 60 * 1000);
    } catch (InterruptedException e) {
    }
  }

  public void sayHelloWorld() {
    sayHelloWorldProxy1();
  }

  private void sayHelloWorldProxy1() {
    sayHelloWorldProxy2();
  }

  private void sayHelloWorldProxy2() {
    sayHelloWorldProxy3();
  }

  private void sayHelloWorldProxy3() {
    sayHelloWorldProxy4();
  }

  private void sayHelloWorldProxy4() {
    sayHelloWorldProxy5();
  }

  private void sayHelloWorldProxy5() {
    sayHelloWorldInSynchronizedArea();
  }

  private synchronized void sayHelloWorldInSynchronizedArea() {
    System.out.println("Hello, world!");
  }
}
```

增加 `-XX:+PreserveFramePointer` 选项后的线程栈：

```text
Thread 21 (Thread 0x7f81b6ec9700 (LWP 11374)):
#0  pthread_cond_timedwait@@GLIBC_2.3.2 () at ../sysdeps/unix/sysv/linux/x86_64/pthread_cond_timedwait.S:225
#1  0x00007f820aabe25e in os::Linux::safe_cond_timedwait (_cond=0x7f819c001d58, _mutex=0x7f819c001d30, _abstime=0x7f81b6ec8110) at /jdk8u/hotspot/src/os/linux/vm/os_linux.cpp:5433
#2  0x00007f820aabfb24 in os::PlatformEvent::park (this=0x7f819c001d00, millis=1000) at /jdk8u/hotspot/src/os/linux/vm/os_linux.cpp:6078
#3  0x00007f820aa95fb2 in ObjectMonitor::EnterI (this=0x7f81c0006368, __the_thread__=0x7f819c001000) at /jdk8u/hotspot/src/share/vm/runtime/objectMonitor.cpp:632
#4  0x00007f820aa956ca in ObjectMonitor::enter (this=0x7f81c0006368, __the_thread__=0x7f819c001000) at /jdk8u/hotspot/src/share/vm/runtime/objectMonitor.cpp:414
#5  0x00007f820abf720a in ObjectSynchronizer::slow_enter (obj=..., lock=0x7f81b6ec8538, __the_thread__=0x7f819c001000) at /jdk8u/hotspot/src/share/vm/runtime/synchronizer.cpp:265
#6  0x00007f820abf6d82 in ObjectSynchronizer::fast_enter (obj=..., lock=0x7f81b6ec8538, attempt_rebias=true, __the_thread__=0x7f819c001000) at /jdk8u/hotspot/src/share/vm/runtime/synchronizer.cpp:183
#7  0x00007f820a7a2a98 in InterpreterRuntime::monitorenter (thread=0x7f819c001000, elem=0x7f81b6ec8538) at /jdk8u/hotspot/src/share/vm/interpreter/interpreterRuntime.cpp:632
#8  0x00007f81f8a0043b in ?? ()
#9  0x00007f81f8a002ec in ?? ()
#10 0x0000000000000003 in ?? ()
#11 0x000000076c65a5e8 in ?? ()
#12 0x00007f81b6ec8538 in ?? ()
#13 0x00007f81f662b958 in ?? ()
#14 0x00007f81b6ec8598 in ?? ()
#15 0x00007f81f662b9d0 in ?? ()
#16 0x0000000000000000 in ?? ()
```

可能是因为 debug 版本的关系，不加 perserve 选项也能看到这些线程栈。

但是通过 perf 看到的栈却少于通过 gdb 看到的栈：

```text
main 11644 [001] 88497.197837:         sched:sched_switch: main:11644 [120] S ==> swapper/1:0 [120]
            7fffa741f537 __schedule+0x8000592022a7 ([kernel.kallsyms])
            7fffa741f537 __schedule+0x8000592022a7 ([kernel.kallsyms])
            7fffa7282981 proc_fork_connector+0x800059202001 ([kernel.kallsyms])
            7fffa741f9b2 schedule+0x800059202032 ([kernel.kallsyms])
            7fffa6efdae1 futex_wait_queue_me+0x8000592020c1 ([kernel.kallsyms])
            7fffa6efe816 futex_wait+0x8000592020f6 ([kernel.kallsyms])
            7fffa6f357c7 ftrace_ops_assist_func+0x8000592020f7 ([kernel.kallsyms])
            7fffa6f70380 perf_event_task_output+0x800059202000 ([kernel.kallsyms])
            7fffa6f734ee perf_iterate_ctx+0x80005920205e ([kernel.kallsyms])
            7fffa6f00a0f do_futex+0x80005920214f ([kernel.kallsyms])
            7fffa6eb5d42 enqueue_task_fair+0x800059202082 ([kernel.kallsyms])
            7fffa6e5e03a kvm_sched_clock_read+0x80005920201a ([kernel.kallsyms])
            7fffa6e318f5 sched_clock+0x800059202005 ([kernel.kallsyms])
            7fffa6e54a79 x2apic_send_IPI+0x800059202049 ([kernel.kallsyms])
            7fffa6ea926e wake_up_new_task+0x80005920214e ([kernel.kallsyms])
            7fffa6f014df sys_futex+0x80005920207f ([kernel.kallsyms])
            7fffa6e65508 __do_page_fault+0x800059202278 ([kernel.kallsyms])
            7fffa6e05b7d do_syscall_64+0x80005920208d ([kernel.kallsyms])
            7fffa742438e entry_SYSCALL_64_after_swapgs+0x800059202058 ([kernel.kallsyms])
                    d17f pthread_cond_wait@@GLIBC_2.3.2+0xffff00e19b6860bf (/lib/x86_64-linux-gnu/libpthread-2.24.so)
                  b94763 os::PlatformEvent::park+0xffff00e19b24c1a1 (/home/demons/build/build/linux-x86_64-normal-server-slowdebug/jdk/lib/amd64/server/libjvm.so)
```

# 查看线程栈：JIT 部分

[Stack Overflow: Understanding perf.map](https://stackoverflow.com/questions/52392319/understanding-perf-map)
