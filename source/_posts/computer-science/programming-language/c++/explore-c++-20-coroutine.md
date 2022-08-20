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
// g++ -std=c++20 -fcoroutines -ggdb -O0 main.cc -o main.o
// objdump -M intel,intel-mnemonic --demangle=auto --no-recurse-limit --no-show-raw-insn -d main.o
#include <concepts>
#include <coroutine>
#include <exception>
#include <iostream>

struct ReturnObject {
  struct promise_type {
    ReturnObject get_return_object() { return {}; }
    std::suspend_never initial_suspend() { return {}; }
    std::suspend_never final_suspend() noexcept { return {}; }
    void unhandled_exception() {}
  };
};

struct Awaiter {
  std::coroutine_handle<>* hp_;
  constexpr bool await_ready() const noexcept { return false; }
  void await_suspend(std::coroutine_handle<> h) { *hp_ = h; }
  constexpr void await_resume() const noexcept {}
};

ReturnObject counter(std::coroutine_handle<>* continuation_out) {
  Awaiter a{continuation_out};
  for (unsigned i = 0;; ++i) {
    co_await a;
    std::cout << "counter: " << i << std::endl;
  }
}

int main() {
  std::coroutine_handle<> h;
  counter(&h);
  for (int i = 0; i < 3; ++i) {
    std::cout << "In main function" << std::endl;
    h();
  }
  h.destroy();
  return 0;
}
```

```bash
# readelf --symbols --wide main.o | grep -E "coroutine_handle.*Frame" | awk '{print $NF}' | sort | uniq
_Z7counterPZ7counterPNSt7__n486116coroutine_handleIvEEE50_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame.actor
_Z7counterPZ7counterPNSt7__n486116coroutine_handleIvEEE50_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame.destroy
# gdb main.o
# (gdb) b _Z7counterPZ7counterPNSt7__n486116coroutine_handleIvEEE50_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame.actor
```

```cpp
// (gdb) ptype *frame_ptr
// coroutine frame
struct counter(std::__n4861::coroutine_handle<void>*).Frame {
  void (*_Coro_resume_fn)(counter(std::__n4861::coroutine_handle<void>*).Frame *);
  void (*_Coro_destroy_fn)(counter(std::__n4861::coroutine_handle<void>*).Frame *);
  std::__n4861::__coroutine_traits_impl<ReturnObject, void>::promise_type _Coro_promise;
  std::__n4861::coroutine_handle<ReturnObject::promise_type> _Coro_self_handle;
  std::__n4861::coroutine_handle<void> *continuation_out;
  unsigned short _Coro_resume_index;
  bool _Coro_frame_needs_free;
  bool _Coro_initial_await_resume_called;
  std::__n4861::suspend_never Is_1_1;
  Awaiter a_1_2;
  unsigned int i_2_3;
  std::__n4861::suspend_never Fs_1_5;
};
// (gdb) ptype frame_ptr->_Coro_promise
struct ReturnObject::promise_type {};
// (gdb) ptype frame_ptr->_Coro_self_handle
struct std::__n4861::coroutine_handle<ReturnObject::promise_type>
[with _Promise = ReturnObject::promise_type] {
  void *_M_fr_ptr;
};
// (gdb) ptype frame_ptr->continuation_out
struct std::__n4861::coroutine_handle<void>
[with _Promise = void] {
  _Promise *_M_fr_ptr;
};
```

## `coroutine_handle` 是一个指向 coroutine frame 的指针

`main` 函数的本地变量 `std::coroutine_handle<> h` 最终是通过 `Awaiter::await_suspend` 函数的语句 `*hp_ = h;` 被赋值的，而参数 `h` 又等于变量 `Frame::_Coro_self_handle` ，所以我们只需要观察 `Frame::_Coro_self_handle` 的类型和值就能确定 `coroutine_handle` 是什么了。

```cpp
// (gdb) ptype frame_ptr->_Coro_self_handle
struct std::__n4861::coroutine_handle<ReturnObject::promise_type>
[with _Promise = ReturnObject::promise_type] {
  void *_M_fr_ptr;
};
```

```text
(gdb) c
Continuing.

Hardware watchpoint 6: *(uint64_t*)0x416ec8

Old value = <unreadable>
New value = 4288176
counter(_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame *) (frame_ptr=0x416eb0)
    at /usr/local/include/c++/12.2.0/main.cc:24
24  ReturnObject counter(std::coroutine_handle<>* continuation_out) {
(gdb) print frame_ptr
$12 = (_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame *) 0x416eb0
(gdb) print frame_ptr->_Coro_self_handle
$13 = {_M_fr_ptr = 0x416eb0}
(gdb) print &frame_ptr->_Coro_self_handle
$14 = (std::__n4861::coroutine_handle<ReturnObject::promise_type> *) 0x416ec8
```

通过 GDB 跟踪 `frame_ptr->_Coro_self_handle` ，可以看到它是一个指向 coroutine frame 的指针，从而说明 `coroutine_handle` 是一个指向 coroutine frame 的指针。

## 分析汇编代码

```assembly
00000000004011f6 <counter(std::__n4861::coroutine_handle<void>*)>:
  ; Save address of previous stack frame.
  4011f6:   push   rbp
  ; RBP/EBP is extended base pointer,
  ; it points to the bottom of current stack frame.
  4011f7:   mov    rbp,rsp
  ; RBX is a callee-saved register.
  4011fa:   push   rbx
  ; RSP/ESP is extended stack pointer,
  ; it points to the top of current stack frame.
  ; Notice stack frame grows from higher address to lower address.
  ; Reserve 40 bytes for local variables.
  4011fb:   sub    rsp,0x28
  ; RDI is the first argument of func counter.
  4011ff:   mov    QWORD PTR [rbp-0x28],rdi
  401203:   mov    QWORD PTR [rbp-0x18],0x0
  40120b:   mov    BYTE PTR [rbp-0x19],0x0
  40120f:   mov    BYTE PTR [rbp-0x1a],0x0

  ; The co_await operator ensures the current state of a function
  ; is bundled up somewhere on the heap and creates a callable object
  ; whose invocation continues execution of the current function.
  ; The current state is coroutine frame.
  ; The callable object is of type std::coroutine_handle<>.
  ; Init coroutine frame:
  ; Allocate 64 bytes.
  401213:   mov    eax,0x40
  ; RDI is the first argument of operator new.
  401218:   mov    rdi,rax
  40121b:   call   401080 <operator new(unsigned long)@plt>
  ; RAX is the result of operator new.
  401220:   mov    QWORD PTR [rbp-0x18],rax
  401224:   mov    rax,QWORD PTR [rbp-0x18]
  ; Set Frame::_Coro_frame_needs_free to true.
  401228:   mov    BYTE PTR [rax+0x2a],0x1
  ; Set Frame::_Coro_resume_fn to actor.
  40122c:   mov    rax,QWORD PTR [rbp-0x18]
  401230:   mov    QWORD PTR [rax],0x4012a9
  ; Set Frame::_Coro_destroy_fn to destory.
  401237:   mov    rax,QWORD PTR [rbp-0x18]
  40123b:   mov    QWORD PTR [rax+0x8],0x401594
  ; Set Frame::continuation_out to the first parameter of func counter,
  ; which is coroutine_handle.
  401243:   mov    rdx,QWORD PTR [rbp-0x28]
  401247:   mov    rax,QWORD PTR [rbp-0x18]
  40124b:   mov    QWORD PTR [rax+0x20],rdx

  40124f:   mov    rax,QWORD PTR [rbp-0x18]
  401253:   add    rax,0x10
  ;   typeof(Frame::_Coro_promise)
  ; = std::__n4861::__coroutine_traits_impl<ReturnObject, void>::promise_type
  ; = ReturnObject::promise_type
  401257:   mov    rdi,rax
  ; Call ReturnObject::promise_type::get_return_object()
  ; with this = &Frame::_Coro_promise.
  40125a:   call   401724 <ReturnObject::promise_type::get_return_object()>
  40125f:   mov    rax,QWORD PTR [rbp-0x18]
  ; Set Frame::_Coro_resume_index to 0.
  401263:   mov    WORD PTR [rax+0x28],0x0
  401269:   mov    rax,QWORD PTR [rbp-0x18]
  ; Call actor(frame).
  40126d:   mov    rdi,rax
  401270:   call   4012a9 <counter(counter(std::__n4861::coroutine_handle<void>*)::_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame*) [clone .actor]>
  ; After actor function returns,
  ; current function returns instead of continuing execution.
  401275:   jmp    4012a3

  401277:   mov    rdi,rax
  40127a:   call   401030 <__cxa_begin_catch@plt>
  40127f:   mov    rax,QWORD PTR [rbp-0x18]
  401283:   mov    rdi,rax
  401286:   call   401060 <operator delete(void*)@plt>
  40128b:   call   4010b0 <__cxa_rethrow@plt>
  401290:   mov    rbx,rax
  401293:   call   4010d0 <__cxa_end_catch@plt>
  401298:   mov    rax,rbx
  40129b:   mov    rdi,rax
  40129e:   call   4010f0 <_Unwind_Resume@plt>
  4012a3:   mov    rbx,QWORD PTR [rbp-0x8]
  4012a7:   leave
  4012a8:   ret
```

```assembly
00000000004012a9 <counter(counter(std::__n4861::coroutine_handle<void>*)::_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame*) [clone .actor]>:
  ; Save address of previous stack frame.
  4012a9:   push   rbp
  ; RBP/EBP is extended base pointer,
  ; it points to the bottom of current stack frame.
  4012aa:   mov    rbp,rsp
  ; RBX is a callee-saved register.
  4012ad:   push   rbx
  ; RSP/ESP is extended stack pointer,
  ; it points to the top of current stack frame.
  ; Notice stack frame grows from higher address to lower address.
  ; Reserve 40 bytes for local variables.
  4012ae:   sub    rsp,0x28

  ; RDI is the first argument of function actor,
  ; which is coroutine frame.
  4012b2:   mov    QWORD PTR [rbp-0x28],rdi

  4012b6:   mov    rax,QWORD PTR [rbp-0x28]
  ; Test if Frame::_Coro_resume_index is an even number.
  4012ba:   movzx  eax,WORD PTR [rax+0x28]
  ; If Frame::_Coro_resume_index is an even number,
  ; then jump to 0x401301.
  4012be:   and    eax,0x1
  4012c1:   test   ax,ax
  4012c4:   je     401301 <[clone .actor]+0x58>

  ; Else if Frame::_Coro_resume_index is an odd number.
  ; Please notice Frame::_Coro_frame_needs_free is always true.
  4012c6:   mov    rax,QWORD PTR [rbp-0x28]
  4012ca:   movzx  eax,WORD PTR [rax+0x28]
  ; switch(Frame::_Coro_resume_index) { case 1,3,5,7 }
  4012ce:   movzx  eax,ax
  ; Free coroutine frame and return if Frame::_Coro_resume_index == 0x7.
  4012d1:   cmp    eax,0x7
  4012d4:   je     4014bb
  ; Throw exception if Frame::_Coro_resume_index > 0x7.
  4012da:   cmp    eax,0x7
  4012dd:   jg     4012ff
  ; Free coroutine frame and return if Frame::_Coro_resume_index == 0x5.
  4012df:   cmp    eax,0x5
  4012e2:   je     401431 <[clone .actor]+0x188>
  ; Throw exception if Frame::_Coro_resume_index > 0x5.
  4012e8:   cmp    eax,0x5
  4012eb:   jg     4012ff <[clone .actor]+0x56>
  ; Free coroutine frame and return if Frame::_Coro_resume_index == 0x1.
  4012ed:   cmp    eax,0x1
  4012f0:   je     4014cf
  ; Free coroutine frame and return if Frame::_Coro_resume_index == 0x3.
  4012f6:   cmp    eax,0x3
  4012f9:   je     4013b0 <[clone .actor]+0x107>
  ; Otherwise, raise invalid opcode exception.
  4012ff:   ud2

  ; If Frame::_Coro_resume_index is an even number.
  401301:   mov    rax,QWORD PTR [rbp-0x28]
  401305:   movzx  eax,WORD PTR [rax+0x28]
  ; switch(Frame::_Coro_resume_index) { case 0,2,4,6 }
  401309:   movzx  eax,ax
  ; Jump to 0x4014bd if Frame::_Coro_resume_index == 0x6.
  40130c:   cmp    eax,0x6
  40130f:   je     4014bd
  ; Throw exception if Frame::_Coro_resume_index > 0x6.
  401315:   cmp    eax,0x6
  401318:   jg     40137c
  ; Jump to 0x401436 if Frame::_Coro_resume_index == 0x4.
  40131a:   cmp    eax,0x4
  40131d:   je     401436
  ; Throw exception if Frame::_Coro_resume_index > 0x4.
  401323:   cmp    eax,0x4
  401326:   jg     40137c
  ; Jump to 0x401337 if Frame::_Coro_resume_index == 0x0.
  401328:   test   eax,eax
  40132a:   je     401337
  ; Jump to 0x4013b5 if Frame::_Coro_resume_index == 0x2.
  40132c:   cmp    eax,0x2
  40132f:   je     4013b5
  ; Otherwise, throw exception.
  401335:   jmp    40137c

  ; Execute the following code when Frame::_Coro_resume_index == 0x0.
  401337:   mov    rbx,QWORD PTR [rbp-0x28]
  ; Call std::coroutine_handle<Promise>::from_address(void* addr)
  ; with addr = &Frame.
  ; frame_address creates a coroutine_handle from a null pointer value or
  ; an underlying address of another coroutine_handle.
  ; Return type of from_address is std::coroutine_handle<Promise>.
  ; The underlying address of return value is addr.
  40133b:   mov    rax,QWORD PTR [rbp-0x28]
  40133f:   mov    rdi,rax
  401342:   call   4017b0 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::from_address(void*)>
  ; RAX is return value of func
  ; std::coroutine_handle<Promise>::from_address(void* addr),
  ; which is equal to addr, which is equal to &Frame.
  ; RBX is set to &Frame at 0x401337.
  ; Set Frame::_Coro_self_handle::_M_fr_ptr to &Frame.
  401347:   mov    QWORD PTR [rbx+0x18],rax
  ; Set Frame::_Coro_initial_await_resume_called to false.
  40134b:   mov    rax,QWORD PTR [rbp-0x28]
  40134f:   mov    BYTE PTR [rax+0x2b],0x0
  ; Call ReturnObject::promise_type::initial_suspend() with
  ; this = &Frame::_Coro_promise.
  401353:   mov    rax,QWORD PTR [rbp-0x28]
  401357:   add    rax,0x10
  40135b:   mov    rdi,rax
  40135e:   call   401730 <ReturnObject::promise_type::initial_suspend()>
  ; Call std::__n4861::suspend_never::await_ready() with this = &Frame::Is_1_1.
  401363:   mov    rax,QWORD PTR [rbp-0x28]
  401367:   add    rax,0x2c
  40136b:   mov    rdi,rax
  40136e:   call   4016f8 <std::__n4861::suspend_never::await_ready() const>
  ; Test if return value is true.
  ; await_ready is an optimization.
  ; If it returns true, then co_await does not suspend the function.
  ; In this example, Awaiter::await_ready() will always return false.
  401373:   xor    eax,0x1
  401376:   test   al,al
  ; Always execute this branch.
  401378:   jne    40137e
  40137a:   jmp    4013b5
  ; Raise invalid opcode exception.
  40137c:   ud2
  ; Set Frame::_Coro_resume_index to 0x2.
  40137e:   mov    rax,QWORD PTR [rbp-0x28]
  401382:   mov    WORD PTR [rax+0x28],0x2
  401388:   mov    rax,QWORD PTR [rbp-0x28]
  40138c:   lea    rbx,[rax+0x2c]
  ; Call coroutine_handle::operator() with this = &Frame::_Coro_self_handle.
  ; Actually, coroutine_handle::operator() just calls this function again.
  ; Resumes the execution of the coroutine to which *this refers.
  401390:   mov    rax,QWORD PTR [rbp-0x28]
  401394:   add    rax,0x18
  401398:   mov    rdi,rax
  40139b:   call   40178e <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  ; Call suspend_never::await_suspend(std::coroutine_handle<>* h) with
  ; this = &Frame::Is_1_1 and h = &Frame::_Coro_self_handle.
  4013a0:   mov    rsi,rax
  4013a3:   mov    rdi,rbx
  4013a6:   call   401708 <std::__n4861::suspend_never::await_suspend(std::__n4861::coroutine_handle<void>) const>
  ; Return and don't free coroutine frame.
  4013ab:   jmp    4014f4

  4013b0:   jmp    4014d0

  ; Execute the following code when Frame::_Coro_resume_index == 0x2.
  4013b5:   mov    rax,QWORD PTR [rbp-0x28]
  ; Set Frame::_Coro_initial_await_resume_called to 1.
  4013b9:   mov    BYTE PTR [rax+0x2b],0x1
  4013bd:   mov    rax,QWORD PTR [rbp-0x28]
  ; &Frame::Is_1_1, whose type is std::__n4861::suspend_never*.
  4013c1:   add    rax,0x2c
  ; Call suspend_never::await_resume() with this = &Frame::Is_1_1.
  4013c5:   mov    rdi,rax
  ; suspend_never::await_resume does nothing.
  4013c8:   call   401718 <std::__n4861::suspend_never::await_resume() const>
  4013cd:   mov    rax,QWORD PTR [rbp-0x28]
  ; &Frame::continuation_out, whose type is std::__n4861::coroutine_handle<void>*.
  4013d1:   mov    rdx,QWORD PTR [rax+0x20]
  4013d5:   mov    rax,QWORD PTR [rbp-0x28]
  ; Set Frame::a_1_2::hp_ to &Frame::continuation_out.
  4013d9:   mov    QWORD PTR [rax+0x30],rdx
  4013dd:   mov    rax,QWORD PTR [rbp-0x28]
  ; Set Frame::i_2_3 to 0x0.
  4013e1:   mov    DWORD PTR [rax+0x38],0x0

  ; What does the following code do?
  ; 1. Set Frame::_Coro_resume_index to 0x4.
  ; 2. Call Awaiter::await_suspend(coroutine_handle<void>).
  ; 3. Return and don't free coroutine frame.
  4013e8:   mov    rax,QWORD PTR [rbp-0x28]
  ; &Frame::a_1_2, whose type is Awaiter.
  4013ec:   add    rax,0x30
  4013f0:   mov    rdi,rax
  ; Call Awaiter::await_ready() with this = &Frame::a_1_2.
  4013f3:   call   401754 <Awaiter::await_ready() const>
  ; Test if return value is true.
  ; await_ready is an optimization.
  ; If it returns true, then co_await does not suspend the function.
  ; In this example, Awaiter::await_ready() will always return false.
  4013f8:   xor    eax,0x1
  4013fb:   test   al,al
  4013fd:   je     401436
  4013ff:   mov    rax,QWORD PTR [rbp-0x28]
  ; Set Frame::_Coro_resume_index to 0x4.
  401403:   mov    WORD PTR [rax+0x28],0x4
  401409:   mov    rax,QWORD PTR [rbp-0x28]
  ; &Frame::a_1_2, whose type is Awaiter.
  40140d:   lea    rbx,[rax+0x30]
  401411:   mov    rax,QWORD PTR [rbp-0x28]
  ; &Frame::_Coro_self_handle, whose type if coroutine_handle<ReturnObject::promise_type>.
  401415:   add    rax,0x18
  ; Call std::__n4861::coroutine_handle::operator() with this = &Frame::_Coro_self_handle.
  401419:   mov    rdi,rax
  40141c:   call   40178e <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  ; Call Awaiter::await_suspend(coroutine_handle<void>) with this = &Frame::a_1_2,
  ; h = return value of std::__n4861::coroutine_handle::operator().
  401421:   mov    rsi,rax
  401424:   mov    rdi,rbx
  401427:   call   401764 <Awaiter::await_suspend(std::__n4861::coroutine_handle<void>)>
  ; Return and don't free coroutine frame.
  40142c:   jmp    4014f4

  401431:   jmp    4014d0

  ; Execute following code when Frame::_Coro_resume_index == 0x4.
  401436:   mov    rax,QWORD PTR [rbp-0x28]
  ; &Frame::a_1_2, whose type is Awaiter*.
  40143a:   add    rax,0x30
  ; Call Awaiter::await_resume() with this = &Frame::a_1_2.
  40143e:   mov    rdi,rax
  401441:   call   401782 <Awaiter::await_resume() const>
  ; The code equivalent to the following code has been omitted:
  ; std::cout << "counter: " << i << std::endl.
  ; Frame::i_2_3, whose type is unsigned int.
  40147a:   mov    eax,DWORD PTR [rax+0x38]
  ; Frame:i_2_3 += 1
  40147d:   lea    edx,[rax+0x1]
  401480:   mov    rax,QWORD PTR [rbp-0x28]
  401484:   mov    DWORD PTR [rax+0x38],edx
  ; 1. Set Frame::_Coro_resume_index to 0x4.
  ; 2. Call Awaiter::await_suspend(coroutine_handle<void>).
  ; 3. Return and don't free coroutine frame.
  401487:   jmp    4013e8

  40148c:   mov    rax,QWORD PTR [rbp-0x28]
  ; Set Frame::_Coro_resume_index to 0x6.
  401490:   mov    WORD PTR [rax+0x28],0x6
  401496:   mov    rax,QWORD PTR [rbp-0x28]
  ; &Frame::Fs_1_5, whose type is std::__n4861::suspend_never*.
  40149a:   lea    rbx,[rax+0x3c]
  40149e:   mov    rax,QWORD PTR [rbp-0x28]
  ; &Frame::_Coro_self_handle, whose type is std::__n4861::coroutine_handle<ReturnObject::promise_type>.
  4014a2:   add    rax,0x18
  4014a6:   mov    rdi,rax
  ; Call std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator()
  ; with this = &Frame::_Coro_self_handle.
  4014a9:   call   40178e <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  ; Call std::__n4861::suspend_never::await_suspend(std::__n4861::coroutine_handle<void>)
  ; with this = &Frame::Fs_1_5 and
  ; h = return value of std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator().
  4014ae:   mov    rsi,rax
  4014b1:   mov    rdi,rbx
  4014b4:   call   401708 <std::__n4861::suspend_never::await_suspend(std::__n4861::coroutine_handle<void>) const>
  ; Return and don't free coroutine frame.
  4014b9:   jmp    4014f4

  4014bb:   jmp    4014d0

  ; Execute following code when Frame::_Coro_resume_index == 0x6.
  4014bd:   mov    rax,QWORD PTR [rbp-0x28]
  ; &Frame::Fs_1_5, whose type is std::__n4861::suspend_never*.
  4014c1:   add    rax,0x3c
  ; Call suspend_never::await_resume with this = &Frame::Fs_1_5.
  4014c5:   mov    rdi,rax
  4014c8:   call   401718 <std::__n4861::suspend_never::await_resume() const>
  ; 1. Free coroutine frame (Frame::_Coro_frame_needs_free is always true).
  ; 2. Return.
  4014cd:   jmp    4014d0

  ; Return and do cleanup jobs if needed.
  4014cf:   nop
  4014d0:   mov    rax,QWORD PTR [rbp-0x28]
  ; Frame::_Coro_frame_needs_free, whose type is bool.
  4014d4:   movzx  eax,BYTE PTR [rax+0x2a]
  ; AL is a part of AX.
  4014d8:   movzx  eax,al
  ; If Frame::_Coro_frame_needs_free is false,
  ; then just return and do nothing.
  4014db:   test   eax,eax
  4014dd:   je     40158d
  ; Else if Frame::_Coro_frame_needs_free is true,
  ; then free coroutine frame,
  ; and return.
  4014e3:   mov    rax,QWORD PTR [rbp-0x28]
  4014e7:   mov    rdi,rax
  4014ea:   call   401060 <operator delete(void*)@plt>
  4014ef:   jmp    40158d

  4014f4:   jmp    40158d

  ; Catch and handle exception.
  4014f9:   mov    rdi,rax
  4014fc:   call   401030 <__cxa_begin_catch@plt>
  401501:   mov    rax,QWORD PTR [rbp-0x28]
  401505:   movzx  eax,BYTE PTR [rax+0x2b]
  401509:   xor    eax,0x1
  40150c:   test   al,al
  40150e:   je     401515
  401510:   call   4010b0 <__cxa_rethrow@plt>
  401515:   mov    rax,QWORD PTR [rbp-0x28]
  401519:   mov    QWORD PTR [rax],0x0
  401520:   mov    rax,QWORD PTR [rbp-0x28]
  401524:   mov    WORD PTR [rax+0x28],0x0
  40152a:   mov    rax,QWORD PTR [rbp-0x28]
  40152e:   add    rax,0x10
  401532:   mov    rdi,rax
  401535:   call   401748 <ReturnObject::promise_type::unhandled_exception()>
  40153a:   call   4010d0 <__cxa_end_catch@plt>

  ; Because we never use co_return operator, the following won't be executed forever?
  40153f:   mov    rax,QWORD PTR [rbp-0x28]
  401543:   mov    QWORD PTR [rax],0x0
  40154a:   mov    rax,QWORD PTR [rbp-0x28]
  40154e:   add    rax,0x10
  401552:   mov    rdi,rax
  401555:   call   40173c <ReturnObject::promise_type::final_suspend()>
  40155a:   mov    rax,QWORD PTR [rbp-0x28]
  40155e:   add    rax,0x3c
  401562:   mov    rdi,rax
  401565:   call   4016f8 <std::__n4861::suspend_never::await_ready() const>
  40156a:   xor    eax,0x1
  40156d:   test   al,al
  40156f:   jne    40148c
  401575:   jmp    4014bd

  40157a:   mov    rbx,rax
  40157d:   call   4010d0 <__cxa_end_catch@plt>
  401582:   mov    rax,rbx
  401585:   mov    rdi,rax
  401588:   call   4010f0 <_Unwind_Resume@plt>
  40158d:   nop
  40158e:   mov    rbx,QWORD PTR [rbp-0x8]
  401592:   leave
  401593:   ret
```

```assembly
0000000000401680 <std::__n4861::coroutine_handle<void>::from_address(void*)>:
  401680:   push   rbp
  401681:   mov    rbp,rsp
  401684:   mov    QWORD PTR [rbp-0x18],rdi
  401688:   mov    QWORD PTR [rbp-0x8],0x0
  401690:   mov    rax,QWORD PTR [rbp-0x18]
  401694:   mov    QWORD PTR [rbp-0x8],rax
  401698:   mov    rax,QWORD PTR [rbp-0x8]
  40169c:   pop    rbp
  40169d:   ret

;   std::coroutine_handle<Promise>::operator()
; = std::coroutine_handle<Promise>::resume
00000000004016ba <std::__n4861::coroutine_handle<void>::resume() const>:
  4016ba:   push   rbp
  4016bb:   mov    rbp,rsp
  4016be:   sub    rsp,0x10
  ; Caller calls this function with this = &Frame::_Coro_self_handle::_M_fr_ptr.
  4016c2:   mov    QWORD PTR [rbp-0x8],rdi
  ; RAX = Frame::_Coro_self_handle::_M_fr_ptr = &Frame.
  4016c6:   mov    rax,QWORD PTR [rbp-0x8]
  ; RAX = Frame::_Coro_resume_fn = &<counter(counter(std::__n4861::coroutine_handle<void>*)::_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame*) [clone .actor]>.
  4016ca:   mov    rax,QWORD PTR [rax]
  ; RDX = <counter(counter(std::__n4861::coroutine_handle<void>*)::_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame*) [clone .actor]>.
  4016cd:   mov    rdx,QWORD PTR [rax]
  4016d0:   mov    rdi,rax
  ; Call actor with parameter_1 = &Frame.
  4016d3:   call   rdx
  4016d5:   nop
  4016d6:   leave
  4016d7:   ret
```

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

Coroutine Overview:

+ [David Mazières: My tutorial and take on C++20 coroutines](https://www.scs.stanford.edu/~dm/blog/c++-coroutines.html)
+ [Mircosoft, The Old New Thing, Debugging coroutine handles: The Microsoft Visual C++ compiler, clang, and gcc](https://devblogs.microsoft.com/oldnewthing/20211007-00/?p=105777)
+ [Microsoft, The Old New Thing, C++ coroutines: The initial and final suspend, and improving our return_value method](https://devblogs.microsoft.com/oldnewthing/20210331-00/?p=105028)
+ [ACCU 2022, Jim Pascoe: How to Use C++20 Coroutines for Networking](https://www.youtube.com/watch?v=ZNttI_WswMU)
+ [ITNEXT, Šimon Tóth: C++20 Coroutines — Complete* Guide](https://itnext.io/c-20-coroutines-complete-guide-7c3fc08db89d)
+ [Stack Overflow: How coroutine_handle<Promise>::from_promise() works in C++](https://stackoverflow.com/questions/58632651/how-coroutine-handlepromisefrom-promise-works-in-c)

Coroutine Frame:

+ [Clang 16.0.0: Debugging C++ Coroutines, coroutine frame](https://clang.llvm.org/docs/DebuggingCoroutines.html#coroutine-frame)
+ [gcc-mirror/gcc: C++ coroutines Initial implementation.](https://github.com/gcc-mirror/gcc/commit/49789fd08378e3ff7a6efd7c4f72b72654259b89)
+ [gcc-mirror/gcc: coroutines.cc](https://github.com/gcc-mirror/gcc/blob/2fa8c4a659a19ec971c80704f48f96c13aae9ac3/gcc/cp/coroutines.cc#L4336)
