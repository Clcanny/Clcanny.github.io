---
layout: post
title: "Dynamic Linking: About Global Strings"
date: 2021-03-12 17:16:31
tags:
  - dynamic linking
---

# 环境

本文使用的环境与 [Dynamic Linking: Introduction To Elf File](https://clcanny.github.io/2020/11/24/dynamic-linking-introduction-to-elf-file/) 使用的环境一致。

```bash
# cat /etc/os-release | head -n 1
PRETTY_NAME="Debian GNU/Linux bullseye/sid"
# g++ --version | head -n 1
g++ (Debian 10.2.1-6) 10.2.1 20210110
```

```bash
g++ -fPIC -ggdb -O0 -shared                                                 \
    -Wl,--dynamic-linker=/root/glibc/build/install/lib/ld-linux-x86-64.so.2 \
    foo.cpp -o libfoo.so
g++ main.cpp                                                                \
    -L$PWD -Wl,-rpath=$PWD                                                  \
    -Wl,--dynamic-linker=/root/glibc/build/install/lib/ld-linux-x86-64.so.2 \
    -lfoo -o main
export LD_LIBRARY_PATH=/usr/lib/x86_64-linux-gnu:/lib/x86_64-linux-gnu
```

# Global Raw String

```cpp
#include <iostream>
const char* var = "var";
void foo() {
    std::cout << var << std::endl;
}
```

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-about-global-strings/global-raw-string.png)

```bash
# readelf --section-headers libfoo.so | grep -E -w "Nr|.got|.data|.rodata" -A1 | grep -v "\-\-"
  [Nr] Name              Type             Address           Offset
       Size              EntSize          Flags  Link  Info  Align
  [14] .rodata           PROGBITS         0000000000002000  00002000
       0000000000000005  0000000000000000   A       0     0     1
  [20] .got              PROGBITS         0000000000003fc0  00002fc0
       0000000000000040  0000000000000008  WA       0     0     8
  [22] .data             PROGBITS         0000000000004038  00003038
       0000000000000010  0000000000000000  WA       0     0     8
```

```bash
# objdump -d -j .text libfoo.so | grep "<_Z3foov>:" -A16
0000000000001135 <_Z3foov>:
    1135:       55                      push   %rbp
    1136:       48 89 e5                mov    %rsp,%rbp
    1139:       48 8b 05 b0 2e 00 00    mov    0x2eb0(%rip),%rax        # 3ff0 <var@@Base-0x50>
    1140:       48 8b 00                mov    (%rax),%rax
    1143:       48 89 c6                mov    %rax,%rsi
    1146:       48 8b 05 9b 2e 00 00    mov    0x2e9b(%rip),%rax        # 3fe8 <_ZSt4cout@GLIBCXX_3.4>
    114d:       48 89 c7                mov    %rax,%rdi
    1150:       e8 fb fe ff ff          callq  1050 <_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc@plt>
    1155:       48 89 c2                mov    %rax,%rdx
    1158:       48 8b 05 99 2e 00 00    mov    0x2e99(%rip),%rax        # 3ff8 <_ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_@GLIBCXX_3.4>
    115f:       48 89 c6                mov    %rax,%rsi
    1162:       48 89 d7                mov    %rdx,%rdi
    1165:       e8 f6 fe ff ff          callq  1060 <_ZNSolsEPFRSoS_E@plt>
    116a:       90                      nop
    116b:       5d                      pop    %rbp
    116c:       c3                      retq
# od --skip-bytes=$((0x4040 - 0x4038 + 0x3038)) --read-bytes=8 --format=xL libfoo.so
0030100 0000000000002001
# od --skip-bytes=$((0x2001 - 0x2000 + 0x2000)) --read-bytes=4 --format=xC -c libfoo.so
0020001  76  61  72  00
          v   a   r  \0
```

```bash
# readelf --wide --relocs libfoo.so
Relocation section '.rela.dyn' at offset 0x598 contains 13 entries:
    Offset             Info             Type               Symbol's Value  Symbol's Name + Addend
0000000000004040  0000000000000008 R_X86_64_RELATIVE                         2001
0000000000003ff0  0000000c00000006 R_X86_64_GLOB_DAT      0000000000004040 var + 0
```

# Global String

```bash
#include <iostream>
const std::string var = "var";
void foo() {
    std::cout << var << std::endl;
}
```

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-about-global-strings/global-string.png)

```bash
(gdb) bt
#0  0x00007ffff7f3304b in std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> >::basic_string(char const*, std::allocator<char> const&) ()
   from /usr/lib/x86_64-linux-gnu/libstdc++.so.6
#1  0x00007ffff7fcb21c in __static_initialization_and_destruction_0 (__initialize_p=1, __priority=65535) at foo.cpp:2
#2  0x00007ffff7fcb27a in _GLOBAL__sub_I_foo.cpp(void) () at foo.cpp:5
#3  0x00007ffff7fe3d4c in call_init (l=<optimized out>, argc=argc@entry=1, argv=argv@entry=0x7fffffffece8, env=env@entry=0x7fffffffecf8) at dl-init.c:72
#4  0x00007ffff7fe3e32 in _dl_init (main_map=0x7ffff7ffe1a0, argc=1, argv=0x7fffffffece8, env=0x7fffffffecf8) at dl-init.c:119
#5  0x00007ffff7fd60ca in _dl_start_user () from /root/glibc/build/install/lib/ld-linux-x86-64.so.2
```

1. glibc 会负责调用 \.init 函数和 \.init\_array 指定的函数；
2. gcc 使用 \.init\_array 指定初始化函数，\.init 函数只是一个空壳。

```cpp
void call_init(struct link_map* l, int argc, char** argv, char** env) {
    // Now run the local constructors.  There are two forms of them:
    // - the one named by DT_INIT
    // - the others in the DT_INIT_ARRAY.
    if (l->l_info[DT_INIT] != nullptr) {
        DL_CALL_DT_INIT(
            l, l->l_addr + l->l_info[DT_INIT]->d_un.d_ptr, argc, argv, env);
    }

    // Next see whether there is an array with initialization functions.
    ElfW(Dyn)* init_array = l->l_info[DT_INIT_ARRAY];
    if (init_array != nullptr) {
        unsigned int jm =
            l->l_info[DT_INIT_ARRAYSZ]->d_un.d_val / sizeof(ElfW(Addr));
        ElfW(Addr)* addrs = (ElfW(Addr)*)(init_array->d_un.d_ptr + l->l_addr);
        for (unsigned int j = 0; j < jm; ++j) {
            ((init_t)addrs[j])(argc, argv, env);
        }
    }
}
```

# Thread Local Raw String

```cpp
#include <iostream>
thread_local const char* tbss_var = nullptr;
thread_local const char* tdata_var = "tdata_var";
void foo() {
    tbss_var = "tbss_var";
    std::cout << tbss_var << std::endl;
    std::cout << tdata_var << std::endl;
}
```

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-about-global-strings/thread-local-raw-string.png)

1. 为了保证 thread local 语义，ld 会将 \.tbss section 和 \.tdata section 中的数据拷贝到线程私有区域，详细信息请参考 [Chao-tic: A Deep dive into (implicit) Thread Local Storage](https://chao-tic.github.io/blog/2018/12/25/tls) ；
2. `__tls_get_addr` 是访问线程私有变量的两种方式之一，访问方式可以通过编译选项（`-ftls-model=initial-exec`）控制，详细信息请参考 [Stack Overflow: What is the performance penalty of C++11 thread\_local variables in GCC 4.8?](https://stackoverflow.com/questions/13106049/what-is-the-performance-penalty-of-c11-thread-local-variables-in-gcc-4-8) ；
3. 使用选项 `-ftls-model=initial-exec` 编译的库带有 `STATIC_TLS` flag ，可以通过命令 `readelf --dynamic <lib> | grep FLAGS` 识别。

# Thread Local String

```cpp
#include <iostream>
#include <string>
thread_local std::string var = "var";
void foo() {
    std::cout << var << std::endl;
}
```

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-about-global-strings/thread-local-string.png)

TLS init funtion 负责调用 thread local string 的构造函数，它使用一个 thread local bool 变量来记录构造函数是否已经被调用过，避免重复调用。

# 参考资料

+ [Chao-tic: A Deep dive into (implicit) Thread Local Storage](https://chao-tic.github.io/blog/2018/12/25/tls)
+ [ELF Handling For Thread-Local Storage](https://uclibc.org/docs/tls.pdf)
+ [Oracle: Thread-Local Storage](https://docs.oracle.com/cd/E19683-01/817-3677/chapter8-1/index.html)
+ [Stack Overflow: What is the performance penalty of C++11 thread\_local variables in GCC 4.8?](https://stackoverflow.com/questions/13106049/what-is-the-performance-penalty-of-c11-thread-local-variables-in-gcc-4-8)
+ [MaskRay: All about thread-local storage](https://maskray.me/blog/2021-02-14-all-about-thread-local-storage)
