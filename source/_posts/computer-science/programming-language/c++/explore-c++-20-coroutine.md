---
layout: post
title: Explore C++20 Coroutine
date: 2022-07-30 13:26:01
categories:
  - [Computer Science, Programming Language, C++]
---

# 测试环境

```bash
# docker run -it gcc:12.2.0-bullseye g++ --version
g++ (GCC) 12.2.0
# docker run -it gcc:12.2.0-bullseye cat /etc/os-release
PRETTY_NAME="Debian GNU/Linux 11 (bullseye)"
NAME="Debian GNU/Linux"
VERSION_ID="11"
VERSION="11 (bullseye)"
VERSION_CODENAME=bullseye
ID=debian
HOME_URL="https://www.debian.org/"
SUPPORT_URL="https://www.debian.org/support"
BUG_REPORT_URL="https://bugs.debian.org/"
```

# 用状态机实现 Coroutine

## 概述

```cpp
// g++ -std=c++20 -fcoroutines -fno-exceptions -fno-asynchronous-unwind-tables -ggdb -O0 main.cc -o main.o
// objdump -M intel,intel-mnemonic --demangle=auto --no-recurse-limit --no-show-raw-insn -d main.o
#include <concepts>
#include <coroutine>
#include <exception>
#include <iostream>

struct ReturnObject {
  struct InitialSuspendNever : public std::suspend_never { char c; };
  struct YieldSuspendAlways : public std::suspend_always { char c; };
  struct FinalSuspendAlways : public std::suspend_always { char c; };

  struct promise_type {
    ReturnObject get_return_object() {
      return {
        .h_ = std::coroutine_handle<promise_type>::from_promise(*this)
      };
    }
    InitialSuspendNever initial_suspend() { return {}; }
    YieldSuspendAlways yield_value(unsigned int value) {
      value_ = value;
      return {};
    }
    void return_value(unsigned int value) {
      value_ = value;
    }
    FinalSuspendAlways final_suspend() noexcept { return {}; }
    void unhandled_exception() {}
    unsigned int value_;
  };
  std::coroutine_handle<promise_type> h_;
};

struct CoAwaitSuspendAlways : public std::suspend_always { char c; };
ReturnObject counter() {
  co_await CoAwaitSuspendAlways();
  unsigned int value_a = 0x12345678;
  co_yield value_a;
  unsigned int value_b = 0x90ABCDEF;
  co_yield value_b;
  unsigned int value_c = 0x98765432;
  co_return value_c;
}

int main() {
  auto h = counter().h_;
  auto& promise = h.promise();
  std::cout << promise.value_ << std::endl;
  h();
  std::cout << promise.value_ << std::endl;
  h();
  std::cout << promise.value_ << std::endl;
  h();
  std::cout << promise.value_ << std::endl;
  h.destroy();
  return 0;
}
```

```bash
# readelf --symbols --wide main.o | grep -E "Frame" | awk '{print $NF}' | sort | uniq
_Z7counterPZ7countervE17_Z7counterv.Frame.actor
_Z7counterPZ7countervE17_Z7counterv.Frame.destroy

(gdb) b _Z7counterPZ7countervE17_Z7counterv.Frame.actor
(gdb) r
(gdb) ptype *frame_ptr
// sizeof(*frame_ptr) = 56 = 0x38
type = struct _Z7counterv.Frame {
  // offset = 0 = 0x0
  void (*_Coro_resume_fn)(_Z7counterv.Frame *);
  // offset = 8 = 0x8
  void (*_Coro_destroy_fn)(_Z7counterv.Frame *);
  // offset = 16 = 0x10
  // ReturnObject::promise_type
  std::__n4861::__coroutine_traits_impl<ReturnObject, void>::promise_type _Coro_promise;
  // offset = 24 = 0x18
  std::__n4861::coroutine_handle<ReturnObject::promise_type> _Coro_self_handle;
  // offset = 32 = 0x20
  // The index represents the progress of the coroutine through its function body.
  unsigned short _Coro_resume_index;
  // offset = 34 = 0x22
  bool _Coro_frame_needs_free;
  // offset = 35 = 0x23
  ReturnObject::InitialSuspendNever Is_1_1;
  // offset = 36 = 0x24
  unsigned int value_a_1_2;
  // offset = 40 = 0x28
  unsigned int value_b_1_2;
  // offset = 44 = 0x2c
  unsigned int value_c_1_2;
  // offset = 48 = 0x30
  CoAwaitSuspendAlways Aw0_2_3;
  // offset = 49 = 0x31
  ReturnObject::YieldSuspendAlways Yd1_2_4;
  // offset = 50 = 0x32
  ReturnObject::YieldSuspendAlways Yd2_2_5;
  // offset = 51 = 0x33
  ReturnObject::FinalSuspendAlways Fs_1_6;
}
```

```assembly
0000000000401196 <counter()>:
  ; Save address of previous stack frame.
  401196:   push   rbp
  ; RBP/EBP is extended base pointer,
  ; it points to the bottom of current stack frame.
  401197:   mov    rbp,rsp
  ; RBX is a callee-saved register.
  40119a:   push   rbx
  ; RSP/ESP is extended stack pointer,
  ; it points to the top of current stack frame.
  ; Notice stack frame grows from higher address to lower address.
  ; Reserve 40 bytes for local variables.
  40119b:   sub    rsp,0x18
  40119f:   mov    QWORD PTR [rbp-0x18],0x0
  4011a7:   mov    BYTE PTR [rbp-0x19],0x0
  4011ab:   mov    BYTE PTR [rbp-0x1a],0x0

  ; The co_await operator ensures the current state of a function
  ; is bundled up somewhere on the heap and creates a callable object
  ; whose invocation continues execution of the current function.
  ; The current state is coroutine frame.
  ; The callable object is of type std::coroutine_handle<>.
  ; Init coroutine frame:
  ; Allocate 56 bytes.
  4011af:   mov    eax,0x38
  ; RDI is the first argument of operator new.
  4011b4:   mov    rdi,rax
  4011b7:   call   401060 <operator new(unsigned long)@plt>
  ; RAX is the result of operator new.
  4011bc:   mov    QWORD PTR [rbp-0x18],rax
  ; Set Frame::_Coro_frame_needs_free to true.
  4011c0:   mov    rax,QWORD PTR [rbp-0x18]
  4011c4:   mov    BYTE PTR [rax+0x22],0x1
  ; Set Frame::_Coro_resume_fn to <counter(_Z7counterv.Frame *)>.
  4011c8:   mov    rax,QWORD PTR [rbp-0x18]
  4011cc:   mov    QWORD PTR [rax],0x401212
  ; Set Frame::_Coro_destroy_fn to <counter(_Z7counterv.Frame *)>.
  4011d3:   mov    rax,QWORD PTR [rbp-0x18]
  4011d7:   mov    QWORD PTR [rax+0x8],0x401534
  ; Prepare return value.
  ; Call promise_type::get_return_object() with this = &Frame::_Coro_promise.
  4011df:   mov    rax,QWORD PTR [rbp-0x18]
  4011e3:   add    rax,0x10
  4011e7:   mov    rdi,rax
  4011ea:   call   401708 <ReturnObject::promise_type::get_return_object()>
  4011ef:   mov    rbx,rax
  ; Set Frame::_Coro_resume_index to 0x0.
  4011f2:   mov    rax,QWORD PTR [rbp-0x18]
  4011f6:   mov    WORD PTR [rax+0x20],0x0
  ; Call actor.
  4011fc:   mov    rax,QWORD PTR [rbp-0x18]
  401200:   mov    rdi,rax
  401203:   call   401212 <counter(counter()::_Z7counterv.Frame*) [clone .actor]>
  401208:   nop
  ; Put return value into RAX.
  401209:   mov    rax,rbx
  40120c:   mov    rbx,QWORD PTR [rbp-0x8]
  401210:   leave
  401211:   ret
```

```assembly
0000000000401212 <counter(counter()::_Z7counterv.Frame*) [clone .actor]>:
  ; Save address of previous stack frame.
  401212:   push   rbp
  ; RBP/EBP is extended base pointer,
  ; it points to the bottom of current stack frame.
  401213:   mov    rbp,rsp
  ; RBX is a callee-saved register.
  401216:   push   rbx
  ; RSP/ESP is extended stack pointer,
  ; it points to the top of current stack frame.
  ; Notice stack frame grows from higher address to lower address.
  ; Reserve 40 bytes for local variables.
  401217:   sub    rsp,0x28

  ; RDI is the first argument of function actor,
  ; which is coroutine frame.
  40121b:   mov    QWORD PTR [rbp-0x28],rdi

  40121f:   mov    rax,QWORD PTR [rbp-0x28]
  ; Test if Frame::_Coro_resume_index is an even number.
  401223:   movzx  eax,WORD PTR [rax+0x20]
  ; If Frame::_Coro_resume_index is an even number,
  ; then jump to 0x40124d.
  401227:   and    eax,0x1
  40122a:   test   ax,ax
  40122d:   je     40124d <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x3b>

  ; Else if Frame::_Coro_resume_index is an odd number.
  ; Please notice Frame::_Coro_frame_needs_free is always true.
  40122f:   mov    rax,QWORD PTR [rbp-0x28]
  401233:   movzx  eax,WORD PTR [rax+0x20]
  ; Throw exception if Frame::_Coro_resume_index > 0xb.
  401237:   movzx  eax,ax
  40123a:   cmp    eax,0xb
  40123d:   ja     40124b <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x39>
  ; Jump to a table entry if Frame::_Coro_resume_index <= 0xb.
  ;           [useless] [useful]
  ; 0x402008: 40124b    40150f
  ; 0x402018: 40124b    4012e1
  ; 0x402028: 40124b    401347
  ; 0x402038: 40124b    4013d0
  ; 0x402048: 40124b    401459
  ; 0x402058: 40124b    4014fb
  40123f:   mov    eax,eax
  401241:   mov    rax,QWORD PTR [rax*8+0x402008]
  401249:   jmp    rax
  ; Otherwise, raise invalid opcode exception.
  40124b:   ud2

  ; If Frame::_Coro_resume_index is an even number.
  40124d:   mov    rax,QWORD PTR [rbp-0x28]
  ; Throw exception if Frame::_Coro_resume_index > 0xa.
  401251:   movzx  eax,WORD PTR [rax+0x20]
  401255:   movzx  eax,ax
  401258:   cmp    eax,0xa
  40125b:   ja     4012ad <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x9b>
  ; Jump to a table entry if Frame::_Coro_resume_index <= 0xa.
  ;           [useful] [useless]
  ; 0x402068: 401269   4012ad
  ; 0x402078: 4012e6   4012ad
  ; 0x402088: 40134c   4012ad
  ; 0x402098: 4013d5   4012ad
  ; 0x4020a8: 40145e   4012ad
  ; 0x4020b8: 4014fd
  40125d:   mov    eax,eax
  40125f:   mov    rax,QWORD PTR [rax*8+0x402068]
  401267:   jmp    rax

  ; Execute the following code when Frame::_Coro_resume_index == 0x0.
  401269:   mov    rbx,QWORD PTR [rbp-0x28]
  ; Call std::coroutine_handle<Promise>::from_address(void* addr)
  ; with addr = &Frame.
  ; frame_address creates a coroutine_handle from a null pointer value or
  ; an underlying address of another coroutine_handle.
  ; Return type of from_address is std::coroutine_handle<Promise>.
  ; The underlying address of return value is addr.
  40126d:   mov    rax,QWORD PTR [rbp-0x28]
  401271:   mov    rdi,rax
  401274:   call   4017ba <std::__n4861::coroutine_handle<ReturnObject::promise_type>::from_address(void*)>
  ; RAX is return value of func
  ; std::coroutine_handle<Promise>::from_address(void* addr),
  ; which is equal to addr, which is equal to &Frame.
  ; RBX is set to &Frame at 0x401269.
  ; Set Frame::_Coro_self_handle::_M_fr_ptr to &Frame.
  401279:   mov    QWORD PTR [rbx+0x18],rax
  ; Call ReturnObject::promise_type::initial_suspend() with
  ; this = &Frame::_Coro_promise.
  40127d:   mov    rax,QWORD PTR [rbp-0x28]
  401281:   add    rax,0x10
  401285:   mov    rbx,QWORD PTR [rbp-0x28]
  401289:   mov    rdi,rax
  40128c:   call   401722 <ReturnObject::promise_type::initial_suspend()>
  ; RBX is set to &Frame at 0x401285.
  ; AL is RAX's 8 low bits, which is the return value of initial_suspend().
  ; Set Frame::Is_1_1 to return value of initial_suspend().
  401291:   mov    BYTE PTR [rbx+0x23],al
  ; Call std::__n4861::suspend_never::await_ready() with this = &Frame::Is_1_1.
  401294:   mov    rax,QWORD PTR [rbp-0x28]
  401298:   add    rax,0x23
  40129c:   mov    rdi,rax
  40129f:   call   4016dc <std::__n4861::suspend_never::await_ready() const>
  ; Test if return value is true.
  ; await_ready is an optimization.
  ; If it returns true, then co_await does not suspend the function.
  ; In this example, suspend_never::await_ready() will always return true.
  4012a4:   xor    eax,0x1
  4012a7:   test   al,al
  ; Always skip this branch.
  4012a9:   jne    4012af <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x9d>
  ; Always execute this branch.
  4012ab:   jmp    4012e6 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0xd4>
  ; Raise invalid opcode exception.
  4012ad:   ud2

  ; Always skip the following code.
  ; Set Frame::_Coro_resume_index to 0x2.
  4012af:   mov    rax,QWORD PTR [rbp-0x28]
  4012b3:   mov    WORD PTR [rax+0x20],0x2
  4012b9:   mov    rax,QWORD PTR [rbp-0x28]
  ; Set RBX to &Frame::Is_1_1.
  4012bd:   lea    rbx,[rax+0x23]
  ; Call coroutine_handle::operator()() with this = &Frame::_Coro_self_handle.
  4012c1:   mov    rax,QWORD PTR [rbp-0x28]
  4012c5:   add    rax,0x18
  4012c9:   mov    rdi,rax
  4012cc:   call   401798 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  4012d1:   mov    rsi,rax
  ; Call suspend_never::await_suspend(handle) with this = &Frame::Is_1_1
  ; and handle = return value of coroutine_handle::operator()(&Frame::_Coro_self_handle).
  4012d4:   mov    rdi,rbx
  4012d7:   call   4016ec <std::__n4861::suspend_never::await_suspend(std::__n4861::coroutine_handle<void>) const>
  4012dc:   jmp    40152d <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x31b>

  ; Execute the following code when Frame::_Coro_resume_index == 0x3.
  4012e1:   jmp    401510 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2fe>

  ; Execute the following code when Frame::_Coro_resume_index == 0x2.
  ; Call suspend_never::await_resume() with this = &Frame::Is_1_1.
  4012e6:   mov    rax,QWORD PTR [rbp-0x28]
  4012ea:   add    rax,0x23
  4012ee:   mov    rdi,rax
  4012f1:   call   4016fc <std::__n4861::suspend_never::await_resume() const>
  ; Set Frame::Aw0_2_3 to 0x0.
  4012f6:   mov    rax,QWORD PTR [rbp-0x28]
  4012fa:   mov    BYTE PTR [rax+0x30],0x0
  ; Call suspend_always::await_ready() with this = &Frame::Aw0_2_3.
  4012fe:   mov    rax,QWORD PTR [rbp-0x28]
  401302:   add    rax,0x30
  401306:   mov    rdi,rax
  401309:   call   4016b0 <std::__n4861::suspend_always::await_ready() const>
  ; Test if return value is true.
  40130e:   xor    eax,0x1
  401311:   test   al,al
  ; Always skip this branch.
  401313:   je     40134c <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x13a>
  ; Always execute this branch.
  ; Set Frame::_Coro_resume_index to 0x4.
  401315:   mov    rax,QWORD PTR [rbp-0x28]
  401319:   mov    WORD PTR [rax+0x20],0x4
  ; Set RBX to &Frame::Aw0_2_3.
  40131f:   mov    rax,QWORD PTR [rbp-0x28]
  401323:   lea    rbx,[rax+0x30]
  ; Call coroutine_handle::operator()() with this = &Frame::_Coro_self_handle.
  401327:   mov    rax,QWORD PTR [rbp-0x28]
  40132b:   add    rax,0x18
  40132f:   mov    rdi,rax
  401332:   call   401798 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  ; Call suspend_always::await_suspend(handle) with this = &Frame::Aw0_2_3
  ; and handle = return value of coroutine_handle::operator()(&Frame::_Coro_self_handle).
  401337:   mov    rsi,rax
  40133a:   mov    rdi,rbx
  40133d:   call   4016c0 <std::__n4861::suspend_always::await_suspend(std::__n4861::coroutine_handle<void>) const>
  401342:   jmp    40152d <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x31b>

  ; Execute the following code when Frame::_Coro_resume_index == 0x5.
  401347:   jmp    401510 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2fe>

  ; Execute the following code when Frame::_Coro_resume_index == 0x4.
  ; Call suspend_always::await_resume() with this = &Frame::Aw0_2_3.
  40134c:   mov    rax,QWORD PTR [rbp-0x28]
  401350:   add    rax,0x30
  401354:   mov    rdi,rax
  401357:   call   4016d0 <std::__n4861::suspend_always::await_resume() const>
  ; Set value_a_1_2 to 0x12345678.
  40135c:   mov    rax,QWORD PTR [rbp-0x28]
  401360:   mov    DWORD PTR [rax+0x24],0x12345678
  ; Call promise_type::yield_value(value) with this = &Frame::_Coro_promise
  ; and value = value_a_1_2.
  401367:   mov    rax,QWORD PTR [rbp-0x28]
  40136b:   lea    rdx,[rax+0x10]
  40136f:   mov    rax,QWORD PTR [rbp-0x28]
  401373:   mov    eax,DWORD PTR [rax+0x24]
  401376:   mov    rbx,QWORD PTR [rbp-0x28]
  40137a:   mov    esi,eax
  40137c:   mov    rdi,rdx
  40137f:   call   401732 <ReturnObject::promise_type::yield_value(unsigned int)>
  ; RBX is set to &Frame at 0x401376.
  ; Set Frame::Yd1_2_4 to return value of yield_value(unsigned int).
  401384:   mov    BYTE PTR [rbx+0x31],al
  ; Call suspend_always::await_ready() with this = &Frame::Yd1_2_4.
  401387:   mov    rax,QWORD PTR [rbp-0x28]
  40138b:   add    rax,0x31
  40138f:   mov    rdi,rax
  401392:   call   4016b0 <std::__n4861::suspend_always::await_ready() const>
  ; Test if return value is true.
  401397:   xor    eax,0x1
  40139a:   test   al,al
  ; Always skip this branch.
  40139c:   je     4013d5 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x1c3>
  ; Always execute this branch.
  ; Set Frame::_Coro_resume_index to 0x6.
  40139e:   mov    rax,QWORD PTR [rbp-0x28]
  4013a2:   mov    WORD PTR [rax+0x20],0x6
  ; Call suspend_always::await_suspend(handle) with this = &Frame::Yd1_2_4
  ; and handle = return value of coroutine_handle::operator()(&Frame::_Coro_self_handle).
  4013a8:   mov    rax,QWORD PTR [rbp-0x28]
  4013ac:   lea    rbx,[rax+0x31]
  4013b0:   mov    rax,QWORD PTR [rbp-0x28]
  4013b4:   add    rax,0x18
  4013b8:   mov    rdi,rax
  4013bb:   call   401798 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  4013c0:   mov    rsi,rax
  4013c3:   mov    rdi,rbx
  4013c6:   call   4016c0 <std::__n4861::suspend_always::await_suspend(std::__n4861::coroutine_handle<void>) const>
  4013cb:   jmp    40152d <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x31b>

  ; Execute the following code when Frame::_Coro_resume_index == 0x7.
  4013d0:   jmp    401510 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2fe>

  ; Execute the following code when Frame::_Coro_resume_index == 0x6.
  ; Call suspend_always::await_resume() with this = &Frame::Yd1_2_4.
  4013d5:   mov    rax,QWORD PTR [rbp-0x28]
  4013d9:   add    rax,0x31
  4013dd:   mov    rdi,rax
  4013e0:   call   4016d0 <std::__n4861::suspend_always::await_resume() const>
  ; Set value_b_1_2 to 0x90abcdef.
  4013e5:   mov    rax,QWORD PTR [rbp-0x28]
  4013e9:   mov    DWORD PTR [rax+0x28],0x90abcdef
  ; Call promise_type::yield_value(value) with this = &Frame::_Coro_promise
  ; and value_b_1_2.
  4013f0:   mov    rax,QWORD PTR [rbp-0x28]
  4013f4:   lea    rdx,[rax+0x10]
  4013f8:   mov    rax,QWORD PTR [rbp-0x28]
  4013fc:   mov    eax,DWORD PTR [rax+0x28]
  4013ff:   mov    rbx,QWORD PTR [rbp-0x28]
  401403:   mov    esi,eax
  401405:   mov    rdi,rdx
  401408:   call   401732 <ReturnObject::promise_type::yield_value(unsigned int)>
  ; Set Frame::Yd2_2_5 to return value of yield_value(unsigned int).
  40140d:   mov    BYTE PTR [rbx+0x32],al
  ; Call suspend_always::await_ready() with this = &Frame::Yd2_2_5.
  401410:   mov    rax,QWORD PTR [rbp-0x28]
  401414:   add    rax,0x32
  401418:   mov    rdi,rax
  40141b:   call   4016b0 <std::__n4861::suspend_always::await_ready() const>
  ; Test if return value is true.
  401420:   xor    eax,0x1
  401423:   test   al,al
  ; Always skip this branch.
  401425:   je     40145e <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x24c>
  ; Always execute this branch.
  ; Call suspend_always::await_suspend(handle) with this = &Frame::Yd2_2_5
  ; and handle = return value of coroutine_handle::operator()(&Frame::_Coro_self_handle).
  401427:   mov    rax,QWORD PTR [rbp-0x28]
  40142b:   mov    WORD PTR [rax+0x20],0x8
  401431:   mov    rax,QWORD PTR [rbp-0x28]
  401435:   lea    rbx,[rax+0x32]
  401439:   mov    rax,QWORD PTR [rbp-0x28]
  40143d:   add    rax,0x18
  401441:   mov    rdi,rax
  401444:   call   401798 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  401449:   mov    rsi,rax
  40144c:   mov    rdi,rbx
  40144f:   call   4016c0 <std::__n4861::suspend_always::await_suspend(std::__n4861::coroutine_handle<void>) const>
  401454:   jmp    40152d <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x31b>

  ; Execute the following code when Frame::_Coro_resume_index == 0x9.
  401459:   jmp    401510 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2fe>

  ; Execute the following code when Frame::_Coro_resume_index == 0x8.
  ; Call suspend_always::await_resume() with this = &Frame::Yd2_2_5.
  40145e:   mov    rax,QWORD PTR [rbp-0x28]
  401462:   add    rax,0x32
  401466:   mov    rdi,rax
  401469:   call   4016d0 <std::__n4861::suspend_always::await_resume() const>
  ; Set value_c_1_2 to 0x98765432.
  40146e:   mov    rax,QWORD PTR [rbp-0x28]
  401472:   mov    DWORD PTR [rax+0x2c],0x98765432
  ; Call promise_type::return_value(value) with this = &Frame::_Coro_promise
  ; and value = value_c_1_2.
  401479:   mov    rax,QWORD PTR [rbp-0x28]
  40147d:   lea    rdx,[rax+0x10]
  401481:   mov    rax,QWORD PTR [rbp-0x28]
  401485:   mov    eax,DWORD PTR [rax+0x2c]
  401488:   mov    esi,eax
  40148a:   mov    rdi,rdx
  40148d:   call   40174e <ReturnObject::promise_type::return_value(unsigned int)>
  401492:   nop
  ; Set Frame::_Coro_resume_fn to nullptr.
  401493:   mov    rax,QWORD PTR [rbp-0x28]
  401497:   mov    QWORD PTR [rax],0x0
  ; Call promise_type::final_suspend() with this = &Frame::_Coro_promise.
  40149e:   mov    rax,QWORD PTR [rbp-0x28]
  4014a2:   add    rax,0x10
  4014a6:   mov    rbx,QWORD PTR [rbp-0x28]
  4014aa:   mov    rdi,rax
  4014ad:   call   401766 <ReturnObject::promise_type::final_suspend()>
  ; RBX is set to &Frame at 0x4014a6.
  ; Set Frame::Fs_1_6 to return value of final_suspend().
  4014b2:   mov    BYTE PTR [rbx+0x33],al
  ; Call suspend_always::await_ready() with this = &Frame::Fs_1_6.
  4014b5:   mov    rax,QWORD PTR [rbp-0x28]
  4014b9:   add    rax,0x33
  4014bd:   mov    rdi,rax
  4014c0:   call   4016b0 <std::__n4861::suspend_always::await_ready() const>
  ; Test if return value is true.
  4014c5:   xor    eax,0x1
  4014c8:   test   al,al
  ; Always skip this branch.
  4014ca:   je     4014fd <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2eb>
  ; Always execute this branch.
  ; Set Frame::_Coro_resume_index to 0xa.
  4014cc:   mov    rax,QWORD PTR [rbp-0x28]
  4014d0:   mov    WORD PTR [rax+0x20],0xa
  ; Call suspend_always::await_suspend(handle) with this = &Frame::Fs_1_6
  ; and handle = return value of coroutine_handle::operator()(&Frame::_Coro_self_handle).
  4014d6:   mov    rax,QWORD PTR [rbp-0x28]
  4014da:   lea    rbx,[rax+0x33]
  4014de:   mov    rax,QWORD PTR [rbp-0x28]
  4014e2:   add    rax,0x18
  4014e6:   mov    rdi,rax
  4014e9:   call   401798 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  4014ee:   mov    rsi,rax
  4014f1:   mov    rdi,rbx
  4014f4:   call   4016c0 <std::__n4861::suspend_always::await_suspend(std::__n4861::coroutine_handle<void>) const>
  4014f9:   jmp    40152d <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x31b>

  ; Execute the following code when Frame::_Coro_resume_index == 0xb.
  4014fb:   jmp    401510 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2fe>

  ; Execute the following code when Frame::_Coro_resume_index == 0xa.
  ; Call suspend_always::await_resume() with this = &Frame::Fs_1_6.
  4014fd:   mov    rax,QWORD PTR [rbp-0x28]
  401501:   add    rax,0x33
  401505:   mov    rdi,rax
  401508:   call   4016d0 <std::__n4861::suspend_always::await_resume() const>
  40150d:   jmp    401510 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2fe>

  ; Execute the following code when Frame::_Coro_resume_index == 0x1.
  40150f:   nop
  ; Execute the following code when Frame::_Coro_resume_index == 0x3/0x5/0x7/0x9/0xb.
  ; Test if Frame::_Coro_frame_needs_free is true.
  401510:   mov    rax,QWORD PTR [rbp-0x28]
  401514:   movzx  eax,BYTE PTR [rax+0x22]
  401518:   movzx  eax,al
  40151b:   test   eax,eax
  ; Jump to 0x40152d if Frame::_Coro_frame_needs_free is false.
  40151d:   je     40152d <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x31b>
  ; Delete coroutine frame.
  40151f:   mov    rax,QWORD PTR [rbp-0x28]
  401523:   mov    rdi,rax
  401526:   call   401050 <operator delete(void*)@plt>
  40152b:   jmp    40152d <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x31b>
  40152d:   nop
  40152e:   mov    rbx,QWORD PTR [rbp-0x8]
  401532:   leave
  401533:   ret
```

## coroutine frame 是一个保存 coroutine 状态的栈

C++20 的 coroutine 是无栈协程，相较于有栈协程，无栈协程不会在堆内存上开一块空间来伪装成调用栈，而是让编译器用一个结构体将参数和本地变量保存下来。[gcc-mirror/gcc: coroutines.cc](https://github.com/gcc-mirror/gcc/blob/2fa8c4a659a19ec971c80704f48f96c13aae9ac3/gcc/cp/coroutines.cc#L4336) 有一段注释描述了 coroutine frame 的大致结构：

```cpp
// We do something like this:
// declare a dummy coro frame.
// struct _R_frame {
//  using handle_type = coro::coroutine_handle<coro1::promise_type>;
//  void (*_Coro_resume_fn)(_R_frame *);
//  void (*_Coro_destroy_fn)(_R_frame *);
//  coro1::promise_type _Coro_promise;
//  bool _Coro_frame_needs_free; free the coro frame mem if set.
//  bool _Coro_i_a_r_c; [dcl.fct.def.coroutine] / 5.3
//  short _Coro_resume_index;
//  handle_type _Coro_self_handle;
//  parameter copies (were required).
//  local variables saved (including awaitables)
//  (maybe) trailing space.
```

## promise 是一个 coroutine 向 caller 传递数据的结构

+ `co_yield` 使 coroutine 调用 `promise_type::yield_value` 。
+ `co_return` 使 coroutine 调用 `promise_type::return_value` 。
+ `initial_suspend` / `final_suspend` 分别控制 coroutine 开始和结束时是否额外暂停一次。

## `coroutine_handle` 是一个指向 coroutine frame 的指针

```text
(gdb) b _Z7counterPZ7countervE17_Z7counterv.Frame.actor
(gdb) r
(gdb) ptype frame_ptr->_Coro_self_handle
struct std::__n4861::coroutine_handle<ReturnObject::promise_type>
[with _Promise = ReturnObject::promise_type] {
  void *_M_fr_ptr;
};
(gdb) watch frame_ptr->_Coro_self_handle
Hardware watchpoint 2: frame_ptr->_Coro_self_handle
(gdb) c
Hardware watchpoint 2: frame_ptr->_Coro_self_handle
Old value = {_M_fr_ptr = 0x0}
New value = {_M_fr_ptr = 0x1ab6eb0}
(gdb) print frame_ptr
$1 = (_Z7counterv.Frame *) 0x1ab6eb0
(gdb) print &frame_ptr->_Coro_resume_fn
$2 = (void (**)(_Z7counterv.Frame *)) 0x1ab6eb0
```

```text
(gdb) b main.cc:47
(gdb) c
Breakpoint 3, main () at /usr/local/include/c++/12.2.0/main.cc:47
47    auto& promise = h.promise();
(gdb) print h
$3 = {_M_fr_ptr = 0x1ab6eb0}
```

通过 GDB 跟踪 `frame_ptr->_Coro_self_handle` ，可以看到它是一个指向 `Frame` / `Frame::_Coro_resume_fn` 的指针，从而说明 `coroutine_handle` 也是一个指向 `Frame` / `Frame::_Coro_resume_fn` 的指针。

## `Awaiter`

[C++ reference: Coroutines](https://en.cppreference.com/w/cpp/language/coroutines) 提到了 `Awaiter` 的作用：

> `co_await expr`:
>
> First, expr is converted to an awaitable as follows...
>
> Then, the awaiter object is obtained, as follows...
>
> Then, `awaiter.await_ready()` is called (this is a short-cut to avoid the cost of suspension if it's known that the result is ready or can be completed synchronously). If its result, contextually-converted to bool is `false` then
>
> + The coroutine is suspended (its coroutine state is populated with local variables and current suspension point).
> + `awaiter.await_suspend(handle)` is called, where handle is the coroutine handle representing the current coroutine. Inside that function, the suspended coroutine state is observable via that handle, and it's this function's responsibility to schedule it to resume on some executor, or to be destroyed (returning `false` counts as scheduling)
>   + if `await_suspend` returns `void`, control is immediately returned to the caller/resumer of the current coroutine (this coroutine remains suspended).
>   + if `await_suspend` returns `bool`,
>     + the value `true` returns control to the caller/resumer of the current coroutine.
>     + the value `false` resumes the current coroutine.
>   + if `await_suspend` returns a coroutine handle for some other coroutine, that handle is resumed (by a call to `handle.resume()`) (note this may chain to eventually cause the current coroutine to resume).
>   + if `await_suspend` throws an exception, the exception is caught, the coroutine is resumed, and the exception is immediately re-thrown.
>
> Finally, `awaiter.await_resume()` is called (whether the coroutine was suspended or not), and its result is the result of the whole `co_await expr` expression.

# 解密 std::coroutine_handle<Promise>::from_promise

`std::coroutine_handle<Promise>::from_promise` 看上去很像“魔法”，从一个没有任何相关字段的对象（比如 `ReturnObject::promise_type` ）里凭空变出了 `coroutine_handle` 。[Stack Overflow: How coroutine_handle<Promise>::from_promise() works in C++](https://stackoverflow.com/questions/58632651/how-coroutine-handlepromisefrom-promise-works-in-c) 解释了这个魔法：

> It works by fiat. That is, it works because the standard says that it works, and implementations must therefore find a way to implement coroutines in such a way that it is possible.
>
> When creating a coroutine, the implementation creates two things: the `coroutine_handle` and the `promise` object. The location of both of these things is controlled entirely by the compiler. So, the compiler could very easily allocate them contiguously with each other, such that a coroutine's stack would essentially start with a `struct {coroutine_handle<Promise> handle; Promise promise};`.
>
> Given that knowledge, you know that the handle for any promise type lives `sizeof(coroutine_handle<Promise>)` bytes before any `promise` object's address (alignment requirements of the `Promise` type can adjust this, but such things can be queried from the type). And since `from_promise` takes a promise object, you can just offset the pointer and cast it to a `coroutine_handle<Promise>`.
>
> Now, that is just one way of doing it; an implementation doesn't have to do it this way. What matters is that the implementation has control over where the promise object lives relative to the coroutine internal data. Or more specifically, the promise lives inside of that internal data. Regardless of how you look at it, the compiler knows everything it needs to in order to convert the address of a promise into the internal data needed to fill in a `coroutine_handle`.


```cpp
// g++ -std=c++20 -fcoroutines -ggdb -O0 main.cc -o main.o
// objdump -M intel,intel-mnemonic --demangle=auto --no-recurse-limit --no-show-raw-insn -d main.o
#include <concepts>
#include <coroutine>
#include <exception>
#include <iostream>

struct ReturnObject {
  struct promise_type {
    ReturnObject get_return_object() {
      return {
        // Uses C++20 designated initializer syntax
        .h_ = std::coroutine_handle<promise_type>::from_promise(*this)
      };
    }
    std::suspend_never initial_suspend() { return {}; }
    std::suspend_never final_suspend() noexcept { return {}; }
    void unhandled_exception() {}
  };

  std::coroutine_handle<promise_type> h_;
  operator std::coroutine_handle<promise_type>() const { return h_; }
  // A coroutine_handle<promise_type> converts to coroutine_handle<>
  operator std::coroutine_handle<>() const { return h_; }
};

ReturnObject counter() {
  for (unsigned i = 0;; ++i) {
    co_await std::suspend_always{};
    std::cout << "counter2: " << i << std::endl;
  }
}

int main() {
  std::coroutine_handle<> h = counter();
  for (int i = 0; i < 3; ++i) {
    std::cout << "In main function" << std::endl;
    h();
  }
  h.destroy();
  return 0;
}
```

```cpp
struct _Z7counterv.Frame {
  void (*_Coro_resume_fn)(_Z7counterv.Frame *);
  void (*_Coro_destroy_fn)(_Z7counterv.Frame *);
  std::__n4861::__coroutine_traits_impl<ReturnObject, void>::promise_type _Coro_promise;
  std::__n4861::coroutine_handle<ReturnObject::promise_type> _Coro_self_handle;
  unsigned short _Coro_resume_index;
  bool _Coro_frame_needs_free;
  bool _Coro_initial_await_resume_called;
  std::__n4861::suspend_never Is_1_1;
  unsigned int i_2_3;
  std::__n4861::suspend_always Aw0_3_4;
  std::__n4861::suspend_never Fs_1_5;
}
```

```assembly
000000000040173c <ReturnObject::promise_type::get_return_object()>:
  40173c:   push   rbp
  40173d:   mov    rbp,rsp
  401740:   sub    rsp,0x10
  401744:   mov    QWORD PTR [rbp-0x8],rdi
  401748:   mov    rax,QWORD PTR [rbp-0x8]
  40174c:   mov    rdi,rax
  40174f:   call   401794 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::from_promise(ReturnObject::promise_type&)>
  401754:   leave
  401755:   ret

0000000000401794 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::from_promise(ReturnObject::promise_type&)>:
  401794:   push   rbp
  401795:   mov    rbp,rsp
  ; RDI = &Frame::_Coro_promise.
  401798:   mov    QWORD PTR [rbp-0x18],rdi
  40179c:   mov    QWORD PTR [rbp-0x8],0x0
  4017a4:   mov    rax,QWORD PTR [rbp-0x18]
  ; RAX = RDI - 0x10 = &Frame::_Coro_promise - 0x10 = &Frame.
  4017a8:   sub    rax,0x10
  4017ac:   mov    QWORD PTR [rbp-0x8],rax
  4017b0:   mov    rax,QWORD PTR [rbp-0x8]
  4017b4:   pop    rbp
  ; Return value is &Frame.
  4017b5:   ret
```

# Reference

Assembly Language:

+ [Intel 64 and IA-32 Architectures Software Developer's Manual: Volume 2](https://www.intel.com/content/www/us/en/architecture-and-technology/64-ia-32-architectures-software-developer-instruction-set-reference-manual-325383.html)
+ [The 64 bit x86 C Calling Convention](https://aaronbloomfield.github.io/pdr/book/x86-64bit-ccc-chapter.pdf)
+ [x86 calling conventions](https://libdl.so/articles/x86_calling_conventions.html)
+ [OSDev.org: CPU Registers x86](https://wiki.osdev.org/CPU_Registers_x86)
+ [Stack Overflow: What are the ESP and the EBP registers?](https://stackoverflow.com/questions/21718397/what-are-the-esp-and-the-ebp-registers)
+ [Stack Overflow: Why does the stack address grow towards decreasing memory addresses?](https://stackoverflow.com/questions/4560720/why-does-the-stack-address-grow-towards-decreasing-memory-addresses)
+ [Stack Overflow: Assembly language je jump function](https://stackoverflow.com/questions/1582960/assembly-language-je-jump-function)

Coroutine proposals:

+ [Open Standards: Working Draft, C++ Extensions for Coroutines](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2018/n4775.pdf)
+ [Open Standards: Coroutines: Language and Implementation Impact](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2019/p1492r0.pdf)
+ [Working Draft, Standard for Programming Language C++: Coroutine definitions](https://eel.is/c++draft/dcl.fct.def.coroutine)

Coroutine Overview:

+ [David Mazières: My tutorial and take on C++20 coroutines](https://www.scs.stanford.edu/~dm/blog/c++-coroutines.html)
+ [Mircosoft, The Old New Thing, Debugging coroutine handles: The Microsoft Visual C++ compiler, clang, and gcc](https://devblogs.microsoft.com/oldnewthing/20211007-00/?p=105777)
+ [Mircosoft, The Old New Thing, C++ coroutines: The mental model for coroutine promises](https://devblogs.microsoft.com/oldnewthing/20210329-00/?p=105015)
+ [Mircosoft, The Old New Thing, C++ coroutines: Basic implementation of a promise type](https://devblogs.microsoft.com/oldnewthing/20210330-00/?p=105019)
+ [Microsoft, The Old New Thing, C++ coroutines: The initial and final suspend, and improving our return_value method](https://devblogs.microsoft.com/oldnewthing/20210331-00/?p=105028)
+ [Microsoft, The Old New Thing, C++ coroutines: What happens if an exception occurs in my return_value?](https://devblogs.microsoft.com/oldnewthing/20210401-00/?p=105043)
+ [ACCU 2022, Jim Pascoe: How to Use C++20 Coroutines for Networking](https://www.youtube.com/watch?v=ZNttI_WswMU)
+ [ITNEXT, Šimon Tóth: C++20 Coroutines — Complete* Guide](https://itnext.io/c-20-coroutines-complete-guide-7c3fc08db89d)
+ [Stack Overflow: How coroutine_handle\<Promise\>::from_promise() works in C++](https://stackoverflow.com/questions/58632651/how-coroutine-handlepromisefrom-promise-works-in-c)
+ [C++ reference: Coroutines](https://en.cppreference.com/w/cpp/language/coroutines)

Coroutine Frame:

+ [Clang 16.0.0: Debugging C++ Coroutines, coroutine frame](https://clang.llvm.org/docs/DebuggingCoroutines.html#coroutine-frame)
+ [gcc-mirror/gcc: C++ coroutines Initial implementation.](https://github.com/gcc-mirror/gcc/commit/49789fd08378e3ff7a6efd7c4f72b72654259b89)
+ [gcc-mirror/gcc: coroutines.cc](https://github.com/gcc-mirror/gcc/blob/2fa8c4a659a19ec971c80704f48f96c13aae9ac3/gcc/cp/coroutines.cc#L4336)
