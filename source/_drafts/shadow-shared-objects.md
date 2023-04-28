[g  Stack Overflow: Determine direct shared object dependencies of a Linux binary?](https://stackoverflow.com/questions/6242761/determine-direct-shared-object-dependencies-of-a-linux-binary/6242792)

[LIEF: How to modify the dynamic entries for a ELF in python?](https://github.com/lief-project/LIEF/issues/118)

[Stack Overflow: How can I obtain a PE file's instructions using Python?](https://stackoverflow.com/questions/29737609/how-can-i-obtain-a-pe-files-instructions-using-python)

[Stack Exchange: Elf x86_64 adding function](https://reverseengineering.stackexchange.com/questions/21910/elf-x86-64-adding-function)

disassembler:

[](https://github.com/RobertDurfee/Disassembler)

[](https://stackoverflow.com/questions/5181268/x86-asm-disassembler-library)

[](https://zydis.re/)

[](https://github.com/vmt/udis86)

```python
import lief

libfoo = lief.parse("libfoo.so")
main = lief.parse("main")
libfoo_text_section = libfoo.get_section(".text")
libfoo_text_section = main.add(libfoo_text_section, True)
libfoo_text_section.segments
main.patch_pltgot("_Z3foov", 0xd000)
main[lief.ELF.DYNAMIC_TAGS.NEEDED].tag = lief.ELF.DYNAMIC_TAGS.DEBUG
main[lief.ELF.DYNAMIC_TAGS.DEBUG].value = 0
main.write("main-hooked")
```

[lief-project/Help: removing a dynamic section entry form an ARM64 so file](https://gitter.im/lief-project/Help?at=5b7bcdd938a12915e4d4a152)

> 对于 NEEDED entries ，一旦调用 remove 就会 remove 掉所有的 entries 。这是有问题的，记得进一个 patch 去修改。

做这件事情有两个方案：

1. .text 和 .text 合并，合成一个 .text （这件事情 LIEF 可能已经做过了）
2. .text 和 .text 不合并

```cpp
// Copyright (c) @ 2020 junbin.rjb.
// All right reserved.
//
// Author: junbin.rjb <837940593@qq.com>
// Created: 2020/10/08
// Description: g++ -std=c++11 shadow.cpp -lLIEF -o shadow

#include <memory>

#include <LIEF/ELF.hpp>

int main() {
    std::unique_ptr<LIEF::ELF::Binary> exec{LIEF::ELF::Parser::parse("main")};
    std::unique_ptr<LIEF::ELF::Binary> libfoo{
        LIEF::ELF::Parser::parse("libfoo.so")};
    const LIEF::ELF::Section& libfoo_text_section =
        libfoo->get_section(".text");
    exec->add(libfoo_text_section, true);
    exec->patch_pltgot("_Z3foov", 0x403000);
    auto dynamic_entries = exec->dynamic_entries();
    exec->remove(dynamic_entries[0]);
    for (int i = 0; i < dynamic_entries.size(); i++) {
    }
    exec->write("main-hooked");
}
```

zydis 的编译有问题，记得进一个 patch 去改。

合并段是做不到的，因为我可以把 rip 赋值给 rax ，然后用 rax 根据相对地址找数据

[](https://stackoverflow.com/questions/1804622/restricting-symbols-to-local-scope-for-linux-executable)

[](https://stackoverflow.com/questions/1821153/segfault-on-c-plugin-library-with-duplicate-symbols)

[](https://www.technovelty.org/c/what-exactly-does-bsymblic-do.html)

[](https://software.intel.com/content/www/us/en/develop/articles/performance-tools-for-software-developers-bsymbolic-can-cause-dangerous-side-effects.html)

分段的方案可以考虑一下：有没有什么特殊的段是不能重复出现的？

`Binary::extend_segment`

加上 ggdb 试试看

extend 带上 ggdb 也不行，说明是这个函数实现得有问题

./sysdeps/x86_64/start.S

```assembly
*__libc_start_main@GOTPCREL(%rip)
```

```bash
(gdb) x/a 0x55555555507a + 0x2f66
0x555555557fe0: 0x7ffff7e41481 <__libc_start_main>
0x555555554000     0x555555555000     0x1000        0x0 /root/test/main
```

```bash
echo $((0x55555555507a - 0x555555554000 + 0x2f66))
16352
0x3fe0
```

读的是 got 表而不是 .got.plt 表

```bash
(gdb) p/x 0x55555555607a + 0x2f66 - 0x555555554000
$1 = 0x4fe0
```

```bash
objdump -d -j .text main
objdump -d -j .text main-hooked
```

果然没有对 rip 相关地址进行修正，导致错误。

zeds 说：There is advanced information for each and every instruction. For example, it provides information on what registers and flags are accessed in what way and the byte offsets of individual fragments of the instruction.

有提供这个信息的话，根据 rip 做修正貌似不是很难。

```cpp
#include <Zydis/Zydis.h>
#include <inttypes.h>
#include <iostream>

int main() {
    ZyanU8 data[] = {0xff, 0x15, 0x7e, 0x2f, 0x00, 0x00};
    // Initialize decoder context
    ZydisDecoder decoder;
    ZydisDecoderInit(
        &decoder, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_ADDRESS_WIDTH_64);
    ZydisDecodedInstruction instruction;
    for (int offset = 0; ZYAN_SUCCESS(ZydisDecoderDecodeBuffer(
             &decoder, data + offset, sizeof(data) - offset, &instruction));
         offset += instruction.length) {
        decltype(instruction.operand_count) i = 0;
        for (; i < instruction.operand_count; i++) {
            const ZydisDecodedOperand& operand = instruction.operands[i];
            if (operand.type == ZYDIS_OPERAND_TYPE_REGISTER &&
                operand.reg.value == ZYDIS_REGISTER_RIP) {
                /* break; */
            }
            if (operand.type == ZYDIS_OPERAND_TYPE_IMMEDIATE) {
                std::cout << "here" << std::endl;
            }
        }
        if (i < instruction.operand_count) {
        }
        std::cout << ZydisMnemonicGetString(instruction.mnemonic) << std::endl;
    }
}
```

以上是搜索 rip 寄存器的代码，说明 Zydis 是可以用的。

[x86-64 指令](http://ref.x86asm.net/)

[opcode_map 用法](https://github.com/zyantific/zydis/issues/89)

https://en.wikipedia.org/wiki/X86_instruction_listings

处理 opcode 可以参考：ZydisFormatterIntelFormatOperandMEM

ZydisCalcAbsoluteAddress

可以考虑实现一个 assembler ：https://github.com/zyantific/zydis/issues/129

https://github.com/zyantific/zydis/issues/145

```cpp
// g++ -std=c++11 -O0 -ggdb print.cpp -lLIEF -lZydis -o print
// for f in $(find /usr/lib -type f | head -n 500); do ./print $f; done | sort | uniq

#include <LIEF/ELF.hpp>
#include <Zydis/Zydis.h>
#include <inttypes.h>
#include <iostream>
#include <memory>
#include <vector>

int main(int argc, char* argv[]) {
    std::unique_ptr<LIEF::ELF::Binary> object{
        LIEF::ELF::Parser::parse(argv[1])};
    const LIEF::ELF::Section& section = object->get_section(".text");
    std::vector<uint8_t> content = section.content();

    ZyanU8* data = content.data();
    // Initialize decoder context
    ZydisDecoder decoder;
    ZydisDecoderInit(
        &decoder, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_ADDRESS_WIDTH_64);
    ZydisDecodedInstruction instruction;
    for (int offset = 0; ZYAN_SUCCESS(ZydisDecoderDecodeBuffer(
             &decoder, data + offset, content.size() - offset, &instruction));
         offset += instruction.length) {
        decltype(instruction.operand_count) i = 0;
        for (; i < instruction.operand_count; i++) {
            const ZydisDecodedOperand& operand = instruction.operands[i];
            if (operand.type == ZYDIS_OPERAND_TYPE_REGISTER &&
                operand.reg.value == ZYDIS_REGISTER_RIP) {
                break;
            }
            if (operand.type == ZYDIS_OPERAND_TYPE_IMMEDIATE) {
            }
        }
        if (i < instruction.operand_count) {
            std::cout << ZydisMnemonicGetString(instruction.mnemonic)
                      << std::endl;
        }
    }
}
```

```bash
call
jb
jbe
jle
jmp
jnb
jnbe
jnle
jns
jnz
js
jz
ret
```

基本上都是跳转指令，比较特殊的就是 int int3

那么我们只要碰到一个处理一个就可以了

## expand

阶段性成果

```cpp
// Copyright (c) @ 2020 junbin.rjb.
// All right reserved.
//
// Author: junbin.rjb <837940593@qq.com>
// Created: 2020/10/11
// Description

#include <LIEF/ELF.hpp>
#include <Zydis/Zydis.h>
#include <cstdint>
#include <ios>
#include <iostream>
#include <memory>
#include <vector>

#define private public
#define protected public

int main(int argc, char* argv[]) {
    std::unique_ptr<LIEF::ELF::Binary> libfoo{
        LIEF::ELF::Parser::parse("libfoo.so")};
    const LIEF::ELF::Section& libfoo_text_section =
        libfoo->get_section(".text");
    std::vector<uint8_t> libfoo_text_section_content =
        libfoo_text_section.content();

    std::unique_ptr<LIEF::ELF::Binary> exec{LIEF::ELF::Parser::parse("main")};
    LIEF::ELF::Section& exec_text_section = exec->get_section(".text");
    const LIEF::ELF::Segment& segment = exec_text_section.segments()[0];
    uint64_t virtual_address = segment.virtual_address();
    size_t content_size = segment.get_content_size();
    std::vector<uint8_t> exec_text_section_content =
        exec_text_section.content();
    exec_text_section_content.insert(exec_text_section_content.end(),
                                     libfoo_text_section_content.begin(),
                                     libfoo_text_section_content.end());
    exec->extend(exec_text_section, libfoo_text_section_content.size());
    exec_text_section.content(exec_text_section_content);

    std::vector<std::string> sections_use_rip_to_relocate{".text"};
    for (const auto& s : sections_use_rip_to_relocate) {
        auto section = exec->get_section(s);
        std::vector<uint8_t> content = section.content();
        auto data = content.data();
        // Initialize decoder context
        ZydisDecoder decoder;
        ZydisDecoderInit(
            &decoder, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_ADDRESS_WIDTH_64);
        ZydisDecodedInstruction instruction;
        for (int offset = 0;
             ZYAN_SUCCESS(ZydisDecoderDecodeBuffer(&decoder,
                                                   data + offset,
                                                   content.size() - offset,
                                                   &instruction));
             offset += instruction.length) {
            decltype(instruction.operand_count) i = 0;
            for (; i < instruction.operand_count; i++) {
                const ZydisDecodedOperand& operand = instruction.operands[i];
                if (operand.type == ZYDIS_OPERAND_TYPE_REGISTER &&
                    operand.reg.value == ZYDIS_REGISTER_RIP) {
                    break;
                }
                /* if (operand.type == ZYDIS_OPERAND_TYPE_MEMORY && */
                /*     operand.mem.disp.has_displacement && */
                /*     operand.mem.disp.value > virtual_address + content_size)
                 * { */
                /*     std::cout << ZydisMnemonicGetString(instruction.mnemonic)
                 */
                /*               << " " << (int)i << std::endl; */
                /* } */
            }
            if (i < instruction.operand_count) {
                if (ZydisMnemonicGetString(instruction.mnemonic) ==
                    std::string("call")) {
                    decltype(instruction.operand_count) j = i - 1;
                    assert(j >= 0 && j < instruction.operand_count);
                    const ZydisDecodedOperand& operand =
                        instruction.operands[j];
                    if (operand.type == ZYDIS_OPERAND_TYPE_MEMORY &&
                        operand.mem.disp.has_displacement &&
                        operand.mem.disp.value >
                            virtual_address + content_size) {
                        uint32_t off = 0;
                        off |= data[offset + 2];
                        off |= (data[offset + 3] * 1L) << 8;
                        off |= (data[offset + 4] * 1L) << 16;
                        off |= (data[offset + 5] * 1L) << 24;
                        std::cout << (off == operand.mem.disp.value)
                                  << std::endl;
                        off += libfoo_text_section_content.size();
                        /* content[offset + 2] = off & 0xFF; */
                        /* content[offset + 3] = (off >> 8) & 0xFF; */
                        /* content[offset + 4] = (off >> 16) & 0xFF; */
                        /* content[offset + 5] = (off >> 24) & 0xFF; */
                        exec->patch_address(
                            section.virtual_address() + offset + 2,
                            std::vector<uint8_t>{off & 0xFF,
                                                 (off >> 8) & 0xFF,
                                                 (off >> 16) & 0xFF,
                                                 (off >> 24) & 0xFF});
                    }
                } else {
                    std::cout << ZydisMnemonicGetString(instruction.mnemonic)
                              << std::endl;
                    /* throw 1; */
                }
            }
        }
        /* std::cout << (int)content[0x26] << std::endl; */
        /* section.content(content); */
        /* std::cout << (int)exec->get_section(s).content()[0x26] << std::endl;
         */
    }

    exec->patch_pltgot("_Z3foov", virtual_address + content_size);
    auto dynamic_entries = exec->dynamic_entries();
    exec->remove(dynamic_entries[0]);
    for (int i = 0; i < dynamic_entries.size(); i++) {
    }
    exec->write("main-hooked");
}
```

```cpp
// Copyright (c) @ 2020 junbin.rjb.
// All right reserved.
//
// Author: junbin.rjb <837940593@qq.com>
// Created: 2020/10/11
// Description

#include <LIEF/ELF.hpp>
#include <Zydis/Zydis.h>
#include <cstdint>
#include <ios>
#include <iostream>
#include <memory>
#include <vector>

int main(int argc, char* argv[]) {
    std::unique_ptr<LIEF::ELF::Binary> libfoo{
        LIEF::ELF::Parser::parse("libfoo.so")};
    const LIEF::ELF::Section& libfoo_text_section =
        libfoo->get_section(".text");
    std::vector<uint8_t> libfoo_text_section_content =
        libfoo_text_section.content();

    std::unique_ptr<LIEF::ELF::Binary> exec{LIEF::ELF::Parser::parse("main")};
    LIEF::ELF::Section& exec_text_section = exec->get_section(".text");
    const LIEF::ELF::Segment& segment = exec_text_section.segments()[0];
    uint64_t virtual_address = segment.virtual_address();
    size_t content_size = segment.get_content_size();
    std::vector<uint8_t> exec_text_section_content =
        exec_text_section.content();
    exec_text_section_content.insert(exec_text_section_content.end(),
                                     libfoo_text_section_content.begin(),
                                     libfoo_text_section_content.end());
    exec->extend(exec_text_section, libfoo_text_section_content.size());
    exec_text_section.content(exec_text_section_content);

    std::vector<std::string> sections_use_rip_to_relocate{".text", ".plt.got"};
    for (const auto& s : sections_use_rip_to_relocate) {
        auto section = exec->get_section(s);
        std::vector<uint8_t> content = section.content();
        auto data = content.data();
        // Initialize decoder context
        ZydisDecoder decoder;
        ZydisDecoderInit(
            &decoder, ZYDIS_MACHINE_MODE_LONG_64, ZYDIS_ADDRESS_WIDTH_64);
        ZydisDecodedInstruction instruction;
        for (int offset = 0;
             ZYAN_SUCCESS(ZydisDecoderDecodeBuffer(&decoder,
                                                   data + offset,
                                                   content.size() - offset,
                                                   &instruction));
             offset += instruction.length) {
            decltype(instruction.operand_count) i = 0;
            /* if (ZydisMnemonicGetString(instruction.mnemonic) == */
            /*     std::string("lea")) { */
            /*     std::cout << "here" << std::endl; */
            /* } */
            for (; i < instruction.operand_count; i++) {
                const ZydisDecodedOperand& operand = instruction.operands[i];
                if (operand.type == ZYDIS_OPERAND_TYPE_REGISTER &&
                    operand.reg.value == ZYDIS_REGISTER_RIP) {
                    break;
                }
                if (operand.type == ZYDIS_OPERAND_TYPE_MEMORY &&
                    // operand.mem.type == ZYDIS_MEMOP_TYPE_AGEN &&
                    operand.mem.base == ZYDIS_REGISTER_RIP) {
                    break;
                }
                /* if (operand.type == ZYDIS_OPERAND_TYPE_MEMORY && */
                /*     operand.mem.disp.has_displacement && */
                /*     operand.mem.disp.value > virtual_address + content_size)
                 * { */
                /*     std::cout << ZydisMnemonicGetString(instruction.mnemonic)
                 */
                /*               << " " << (int)i << std::endl; */
                /* } */
            }
            if (i < instruction.operand_count) {
                if (ZydisMnemonicGetString(instruction.mnemonic) ==
                    std::string("call")) {
                    for (i = 0; i < instruction.operand_count; i++) {
                        const ZydisDecodedOperand& operand =
                            instruction.operands[i];
                        if (operand.type == ZYDIS_OPERAND_TYPE_REGISTER &&
                            operand.reg.value == ZYDIS_REGISTER_RIP) {
                            break;
                        }
                    }
                    decltype(instruction.operand_count) j = i - 1;
                    if (!(j >= 0 && j < instruction.operand_count)) {
                        continue;
                    }
                    const ZydisDecodedOperand& operand =
                        instruction.operands[j];
                    // TODO(junbin.rjb)
                    // Fix, rip + operand.mem.disp.value.
                    if (operand.type == ZYDIS_OPERAND_TYPE_MEMORY &&
                        operand.mem.disp.has_displacement) {
                        /* operand.mem.disp.value > */
                        /*     virtual_address + content_size) { */
                        uint32_t off = 0;
                        off |= data[offset + 2];
                        off |= (data[offset + 3] * 1L) << 8;
                        off |= (data[offset + 4] * 1L) << 16;
                        off |= (data[offset + 5] * 1L) << 24;
                        std::cout << (off == operand.mem.disp.value)
                                  << std::endl;
                        off += libfoo_text_section_content.size();
                        /* content[offset + 2] = off & 0xFF; */
                        /* content[offset + 3] = (off >> 8) & 0xFF; */
                        /* content[offset + 4] = (off >> 16) & 0xFF; */
                        /* content[offset + 5] = (off >> 24) & 0xFF; */
                        exec->patch_address(
                            section.virtual_address() + offset + 2,
                            std::vector<uint8_t>{off & 0xFF,
                                                 (off >> 8) & 0xFF,
                                                 (off >> 16) & 0xFF,
                                                 (off >> 24) & 0xFF});
                    }
                } else if (ZydisMnemonicGetString(instruction.mnemonic) ==
                           std::string("lea")) {
                    decltype(instruction.operand_count) j = i;
                    const ZydisDecodedOperand& operand =
                        instruction.operands[j];
                    if (operand.type == ZYDIS_OPERAND_TYPE_MEMORY &&
                        // operand.mem.type == ZYDIS_MEMOP_TYPE_AGEN &&
                        operand.mem.base == ZYDIS_REGISTER_RIP &&
                        operand.mem.disp.has_displacement) {
                        /* section.virtual_address() + offset + 6 + */
                        /*         operand.mem.disp.value > */
                        /*     virtual_address + content_size) { */
                        uint32_t off = 0;
                        off |= data[offset + 3];
                        off |= (data[offset + 4] * 1L) << 8;
                        off |= (data[offset + 5] * 1L) << 16;
                        off |= (data[offset + 6] * 1L) << 24;
                        std::cout << (off == operand.mem.disp.value)
                                  << std::endl;
                        off += libfoo_text_section_content.size();
                        exec->patch_address(
                            section.virtual_address() + offset + 3,
                            std::vector<uint8_t>{off & 0xFF,
                                                 (off >> 8) & 0xFF,
                                                 (off >> 16) & 0xFF,
                                                 (off >> 24) & 0xFF});
                    }
                }
            }
            /* std::cout << (int)content[0x26] << std::endl; */
            /* section.content(content); */
            /* std::cout << (int)exec->get_section(s).content()[0x26] <<
             * std::endl;
             */
        }

        exec->patch_pltgot("_Z3foov", virtual_address + content_size);
        auto dynamic_entries = exec->dynamic_entries();
        exec->remove(dynamic_entries[0]);
        for (int i = 0; i < dynamic_entries.size(); i++) {
        }
        exec->write("main-hooked");
    }
}
```

为什么 `__libc_csu_fini` 的地址从 0x555555555190 变成 0x555555555190 + 64

并没有，不知道为什么 debug 信息错了

0x555555555190 <__libc_csu_fini>:       0x8ec8348000000c3

0x555555555190 <__libc_csu_init+32>:    0xc3

这个差别仅仅是因为后面的内容不一样了而已，从函数来说，是一致的



  >│0x555555555141 <__libc_csu_init+17>     lea    0x2ca0(%rip),%r12        # 0x555555557de8                      │
  >│0x555555555148 <__libc_csu_init+24>     push   %rbp                                                           │
  >│0x555555555149 <__libc_csu_init+25>     lea    0x2ca0(%rip),%rbp        # 0x555555557df0



 >│0x555555555141 <__do_global_dtors_aux+33>       lea    0x2ce0(%rip),%r12        # 0x555555557e28              │
 >│0x555555555148 <__do_global_dtors_aux+40>       push   %rbp                                                   │
 >│0x555555555149 <__do_global_dtors_aux+41>       lea    0x2ce0(%rip),%rbp        # 0x555555557e30



这两段代码有点问题。

https://stackoverflow.com/questions/5459581/how-to-break-on-assembly-instruction-at-a-given-address-in-gdb

readelf --debug-dump=info main

https://stackoverflow.com/questions/7098173/how-can-i-know-what-type-of-debug-info-is-in-an-elf-object-file

先把 debug info 修了

另外：在 .text 段之下的其它段，如果用了相对定位，也会受到印象的

https://eli.thegreenplace.net/2011/12/26/the-contents-of-dwarf-sections

readelf --debug-dump=aranges main
Contents of the .debug_aranges section:

  Length:                   44
  Version:                  2
  Offset into .debug_info:  0x0
  Pointer Size:             8
  Segment Size:             0

    Address            Length
    0000000000001125 000000000000000b
    0000000000000000 0000000000000000
https://sourceware.org/binutils/docs/binutils/readelf.html

readelf --symbols main

.symtab 里面存的信息才是关键

以 <register_tm_clones> 为例，函数的起始地址就不对了

是的，都怪 symtab ，应该是 LIEF 画蛇添足做了修改

src/ELF/Binary.cpp:Binary::extend vs src/ELF/Binary.tcc:extend_segment

Binary.cpp 的实现有一点问题

cmake -DCMAKE_BUILD_TYPE=Debug ..



# Describe the bug

## Source file

```cpp
// main.cpp
int main() {}
```

```cpp
// extend.cpp
// g++ -std=c++11 -O0 -ggdb extend.cpp -lLIEF -o extend
#include <LIEF/ELF.hpp>
#include <memory>
int main() {
    std::unique_ptr<LIEF::ELF::Binary> binary{LIEF::ELF::Parser::parse("main")};
    binary->extend(binary->get_section(".text"), 64);
    binary->write("main-extended");
}
```

## Take a look at .text section

```bash
# objdump -d -j .text main | grep ">:" -A1 | grep -v "\-\-"
0000000000000530 <_start>:
 530:	31 ed                	xor    %ebp,%ebp
0000000000000560 <deregister_tm_clones>:
 560:	48 8d 3d c1 0a 20 00 	lea    0x200ac1(%rip),%rdi        # 201028 <__TMC_END__>
00000000000005a0 <register_tm_clones>:
 5a0:	48 8d 3d 81 0a 20 00 	lea    0x200a81(%rip),%rdi        # 201028 <__TMC_END__>
00000000000005f0 <__do_global_dtors_aux>:
 5f0:	80 3d 31 0a 20 00 00 	cmpb   $0x0,0x200a31(%rip)        # 201028 <__TMC_END__>
0000000000000630 <frame_dummy>:
 630:	48 8d 3d e1 07 20 00 	lea    0x2007e1(%rip),%rdi        # 200e18 <__JCR_END__>
0000000000000660 <main>:
 660:	55                   	push   %rbp
0000000000000670 <__libc_csu_init>:
 670:	41 57                	push   %r15
00000000000006e0 <__libc_csu_fini>:
 6e0:	f3 c3                	repz retq
```

```bash
objdump -d -j .text main-extended | grep ">:" -A1 | grep -v "\-\-"
0000000000000530 <_start>:
 530:	31 ed                	xor    %ebp,%ebp
0000000000000560 <deregister_tm_clones>:
 560:	48 8d 3d c1 0a 20 00 	lea    0x200ac1(%rip),%rdi        # 201028 <_Jv_RegisterClasses>
00000000000005e0 <register_tm_clones>:
 5e0:	5d                   	pop    %rbp
0000000000000630 <__do_global_dtors_aux>:
 630:	48 8d 3d e1 07 20 00 	lea    0x2007e1(%rip),%rdi        # 200e18 <__FRAME_END__+0x2005a0>
0000000000000670 <frame_dummy>:
 670:	41 57                	push   %r15
00000000000006a0 <main>:
 6a0:	ff 48 85             	decl   -0x7b(%rax)
00000000000006b0 <__libc_csu_init>:
 6b0:	4c 89 ea             	mov    %r13,%rdx
0000000000000720 <__libc_csu_fini>:
```

After extending .text section, functions in .text section are wrong. Actually this is cause by wrong records in .symtab section.

Take `register_tm_clones` and `__do_global_dtors_aux` as examples:

```bash
# objdump -d -j .text main-extended | grep "5a0"
 5a0:	48 8d 3d 81 0a 20 00 	lea    0x200a81(%rip),%rdi        # 201028 <_Jv_RegisterClasses>
# objdump -d -j .text main-extended | grep "5f0"
0000000000000630 <__do_global_dtors_aux>:
 5f0:	80 3d 31 0a 20 00 00 	cmpb   $0x0,0x200a31(%rip)        # 201028 <_Jv_RegisterClasses>
```

+ Start address of `register_tm_clones` in main-extended isn't 0x5e0, it is 0x5a0 (just as start address of `register_tm_clones` in main).
+ Start address of `__do_global_dtors_aux` in main-extended isn't 0x630, it is 0x5f0 (just as start address of `__do_global_dtors_aux` in main).

## Root cause

```bash
# readelf --symbols main | grep register_tm_clones
    35: 00000000000005a0     0 FUNC    LOCAL  DEFAULT   13 register_tm_clones
# readelf --symbols main-extended | grep register_tm_clones
    35: 00000000000005e0     0 FUNC    LOCAL  DEFAULT   13 register_tm_clones
```

```bash
# readelf --symbols main | grep __do_global_dtors_aux
    36: 00000000000005f0     0 FUNC    LOCAL  DEFAULT   13 __do_global_dtors_aux
# readelf --symbols main-extended | grep __do_global_dtors_aux
    36: 0000000000000630     0 FUNC    LOCAL  DEFAULT   13 __do_global_dtors_aux
```

I think the root cause is the records in .symtab is wrong.

```cpp
// src/ELF/Binary.cpp
Section& Binary::extend(const Section& section, uint64_t size) {
  // ...
  uint64_t from_address = section_to_extend->virtual_address() + size;
  this->datahandler_->make_hole(
    	section_to_extend->offset() + section_to_extend->size(),
    	size);
  this->shift_symbols(from_address, shift);
}
```

And I compare `Binary::extend` with `Binary::extend_segment`: 

```cpp
// src/ELF/Binary.tcc
uint64_t from_address = segment_to_extend->virtual_address() + segment_to_extend->virtual_size();
this->datahandler_->make_hole(segment_to_extend->file_offset() + segment_to_extend->physical_size(), size);
this->shift_symbols(from_address, shift);
```

## Expected behavior
A clear and concise description of what you expected to happen.

In the above example, start addresses of functions shouldn't change.

And I think `uint64_t from_address = section_to_extend->virtual_address() + size;` need to be `uint64_t from_address = section_to_extend->virtual_address() + section_to_extend->virtual_size();`.

## Environment (please complete the following information):
 - Kernal version: 4.9.0-9-amd64
 - System and Version : Debian GNU/Linux 9 (stretch)
 - Target format: ELF
 - LIEF commit version: 3bd530b8800d79ff20ab04247009d1ecd55cdf49