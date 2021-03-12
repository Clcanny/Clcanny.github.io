---
layout: post
title: "Dynamic Linking: About Global Strings"
date: 2021-03-12 17:16:31
tags:
  - dynamic linking
---

# 环境

```bash
# cat /etc/os-release | head -n 1
PRETTY_NAME="Debian GNU/Linux bullseye/sid"
# g++ --version | head -n 1
g++ (Debian 10.2.1-6) 10.2.1 20210110
```

# Non-static Global Raw String

```cpp
# cat foo.cpp
#include <iostream>
const char* var = "var";
void foo() {
    std::cout << var << std::endl;
}
```

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/dynamic-linking-about-global-strings/non-static-global-raw-string.png)

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
