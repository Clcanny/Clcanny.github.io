---
layout: post
title: Explore C++20 Coroutine
date: 2022-07-30 13:26:01
categories:
  - [Computer Science, Programming Language, C++]
---

```cpp
// g++ -std=c++20 -fcoroutines -ggdb -O0 main.cc -o main.o
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
objdump -M intel,intel-mnemonic --demangle=auto --no-recurse-limit --no-show-raw-insn -d main.o
```

```assembly
00000000004011f6 <_Z7counterPNSt7__n486116coroutine_handleIvEE>:
; counter(std::__n4861::coroutine_handle<void>*)
  4011f6:  push   %rbp       ; Save address of previous stack frame.
  4011f7:  mov    %rsp,%rbp  ; RBP/EBP is extended base pointer,
                             ; it points to the bottom of current stack frame.
  4011fa:  push   %rbx       ; RBX is a callee-saved register.
  4011fb:  sub    $0x28,%rsp ; RSP/ESP is extended stack pointer,
                             ; it points to the top of current stack frame.
                             ; Notice stack frame grows from higher address to lower address.
                             ; Reserve 40 bytes for local variables.
  4011ff:  mov    %rdi,-0x28(%rbp) ; RDI is the first argument of func counter.
  401203:  movq   $0x0,-0x18(%rbp)
  40120b:  movb   $0x0,-0x19(%rbp)
  40120f:  movb   $0x0,-0x1a(%rbp)

                                      ; The co_await operator ensures the current state of a function
                                      ; is bundled up somewhere on the heap and creates a callable object
                                      ; whose invocation continues execution of the current function.
                                      ; The current state is coroutine frame.
                                      ; The callable object is of type std::coroutine_handle<>.
                                      ; Init coroutine frame:
  401213:  mov    $0x40,%eax          ; Allocate 64 bytes.
  401218:  mov    %rax,%rdi           ; RDI is the first argument of operator new.
  40121b:  callq  401080 <_Znwm@plt>  ; operator new(unsigned long)
  401220:  mov    %rax,-0x18(%rbp)    ; RAX is the result of operator new.
  401224:  mov    -0x18(%rbp),%rax    ;
  401228:  movb   $0x1,0x2a(%rax)     ; Set Frame::_Coro_frame_needs_free to true.
  40122c:  mov    -0x18(%rbp),%rax    ;
  401230:  movq   $0x4012a9,(%rax)    ; Set Frame::_Coro_resume_fn to actor.
  401237:  mov    -0x18(%rbp),%rax    ;
  40123b:  movq   $0x401594,0x8(%rax) ; Set Frame::_Coro_destroy_fn to destory.
  401243:  mov    -0x28(%rbp),%rdx    ;
  401247:  mov    -0x18(%rbp),%rax    ; Set Frame::continuation_out,
  40124b:  mov    %rdx,0x20(%rax)     ; which is the first parameter of func counter.

  40124f:  mov    -0x18(%rbp),%rax ;
  401253:  add    $0x10,%rax       ;
  401257:  mov    %rax,%rdi        ; type(Frame::_Coro_promise)
                                   ; = std::__n4861::__coroutine_traits_impl<ReturnObject, void>::promise_type
                                   ; = ReturnObject::promise_type
  40125a:  callq  401718 <_ZN12ReturnObject12promise_type17get_return_objectEv>
                                   ; Call ReturnObject::promise_type::get_return_object()
                                   ; with this = &Frame::_Coro_promise.

  40125f:  mov    -0x18(%rbp),%rax ;
  401263:  movw   $0x0,0x28(%rax)  ; Set Frame::_Coro_resume_index to 0.
  401269:  mov    -0x18(%rbp),%rax ;
  40126d:  mov    %rax,%rdi        ; Call actor(frame).
  401270:  callq  4012a9 <_Z7counterPZ7counterPNSt7__n486116coroutine_handleIvEEE50_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame.actor>
  401275:  jmp    4012a3 <_Z7counterPNSt7__n486116coroutine_handleIvEE+0xad>
                                   ; After actor function returns,
                                   ; current function returns instead of continuing execution.

  401277:  mov    %rax,%rdi
  40127a:  callq  401030 <__cxa_begin_catch@plt>
  40127f:  mov    -0x18(%rbp),%rax
  401283:  mov    %rax,%rdi
  401286:  callq  401060 <_ZdlPv@plt>
  40128b:  callq  4010b0 <__cxa_rethrow@plt>
  401290:  mov    %rax,%rbx
  401293:  callq  4010d0 <__cxa_end_catch@plt>
  401298:  mov    %rbx,%rax
  40129b:  mov    %rax,%rdi
  40129e:  callq  4010f0 <_Unwind_Resume@plt>
  4012a3:  mov    -0x8(%rbp),%rbx
  4012a7:  leaveq
  4012a8:  retq
```

```cpp
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
```

```assembly
00000000004012a9 <counter(counter(std::__n4861::coroutine_handle<void>*)::_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame*) [clone .actor]>:
  4012a9:   push   rbp      ; Save address of previous stack frame.
  4012aa:   mov    rbp,rsp  ; RBP/EBP is extended base pointer,
                            ; it points to the bottom of current stack frame.
  4012ad:   push   rbx      ; RBX is a callee-saved register.
  4012ae:   sub    rsp,0x28 ; RSP/ESP is extended stack pointer,
                            ; it points to the top of current stack frame.
                            ; Notice stack frame grows from higher address to lower address.
                            ; Reserve 40 bytes for local variables.

  4012b2:   mov    QWORD PTR [rbp-0x28],rdi ; RDI is the first argument of function actor,
                                            ; which is coroutine frame.

  4012b6:   mov    rax,QWORD PTR [rbp-0x28]
  4012ba:   movzx  eax,WORD PTR [rax+0x28] ; Test if Frame::_Coro_resume_index is an even number.
  4012be:   and    eax,0x1                 ; If Frame::_Coro_resume_index is an even number,
  4012c1:   test   ax,ax                   ; then jump to 0x401301.
  4012c4:   je     401301 <[clone .actor]+0x58>

  4012c6:   mov    rax,QWORD PTR [rbp-0x28]      ; Else if Frame::_Coro_resume_index is an odd number.
  4012ca:   movzx  eax,WORD PTR [rax+0x28]
  4012ce:   movzx  eax,ax                        ; switch(Frame::_Coro_resume_index) { case 1,3,5,7 }
  4012d1:   cmp    eax,0x7                       ; 1. Free coroutine frame if Frame::_Coro_frame_needs_free is true.
  4012d4:   je     4014bb                        ; 2. Return.
  4012da:   cmp    eax,0x7
  4012dd:   jg     4012ff <[clone .actor]+0x56>  ; Throw exception if Frame::_Coro_resume_index > 0x7.
  4012df:   cmp    eax,0x5                       ; 1. Free coroutine frame if Frame::_Coro_frame_needs_free is true.
  4012e2:   je     401431 <[clone .actor]+0x188> ; 2. Return.
  4012e8:   cmp    eax,0x5
  4012eb:   jg     4012ff <[clone .actor]+0x56>  ; Throw exception if Frame::_Coro_resume_index > 0x5.
  4012ed:   cmp    eax,0x1                       ; 1. Free coroutine frame if Frame::_Coro_frame_needs_free is true.
  4012f0:   je     4014cf                        ; 2. Return.
  4012f6:   cmp    eax,0x3                       ; 1. Free coroutine frame if Frame::_Coro_frame_needs_free is true.
  4012f9:   je     4013b0 <[clone .actor]+0x107> ; 2. Return.
  4012ff:   ud2                                  ; Raise invalid opcode exception.

  401301:   mov    rax,QWORD PTR [rbp-0x28]
  401305:   movzx  eax,WORD PTR [rax+0x28]
  401309:   movzx  eax,ax ; switch(Frame::_Coro_resume_index) { case 2,4,6 }
  40130c:   cmp    eax,0x6
  40130f:   je     4014bd
  401315:   cmp    eax,0x6
  401318:   jg     40137c ; Throw exception if Frame::_Coro_resume_index > 0x6.
  40131a:   cmp    eax,0x4
  40131d:   je     401436
  401323:   cmp    eax,0x4
  401326:   jg     40137c ; Throw exception if Frame::_Coro_resume_index > 0x4.
  401328:   test   eax,eax
  40132a:   je     401337
  40132c:   cmp    eax,0x2
  40132f:   je     4013b5
  401335:   jmp    40137c ; Throw exception if Frame::_Coro_resume_index == 0x0.
  401337:   mov    rbx,QWORD PTR [rbp-0x28]
  40133b:   mov    rax,QWORD PTR [rbp-0x28]
  40133f:   mov    rdi,rax
  401342:   call   4017b0 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::from_address(void*)>
  401347:   mov    QWORD PTR [rbx+0x18],rax
  40134b:   mov    rax,QWORD PTR [rbp-0x28]
  40134f:   mov    BYTE PTR [rax+0x2b],0x0
  401353:   mov    rax,QWORD PTR [rbp-0x28]
  401357:   add    rax,0x10
  40135b:   mov    rdi,rax
  40135e:   call   401730 <ReturnObject::promise_type::initial_suspend()>
  401363:   mov    rax,QWORD PTR [rbp-0x28]
  401367:   add    rax,0x2c
  40136b:   mov    rdi,rax
  40136e:   call   4016f8 <std::__n4861::suspend_never::await_ready() const>
  401373:   xor    eax,0x1
  401376:   test   al,al
  401378:   jne    40137e
  40137a:   jmp    4013b5
  40137c:   ud2           ; Raise invalid opcode exception.

  40137e:   mov    rax,QWORD PTR [rbp-0x28]
  401382:   mov    WORD PTR [rax+0x28],0x2
  401388:   mov    rax,QWORD PTR [rbp-0x28]
  40138c:   lea    rbx,[rax+0x2c]
  401390:   mov    rax,QWORD PTR [rbp-0x28]
  401394:   add    rax,0x18
  401398:   mov    rdi,rax
  40139b:   call   40178e <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  4013a0:   mov    rsi,rax
  4013a3:   mov    rdi,rbx
  4013a6:   call   401708 <std::__n4861::suspend_never::await_suspend(std::__n4861::coroutine_handle<void>) const>
  4013ab:   jmp    4014f4 ; Return and don't free coroutine frame.
  4013b0:   jmp    4014d0

  4013b5:   mov    rax,QWORD PTR [rbp-0x28] ; When Frame::_Coro_resume_index == 2.
  4013b9:   mov    BYTE PTR [rax+0x2b],0x1  ; Set Frame::_Coro_initial_await_resume_called to 1.
  4013bd:   mov    rax,QWORD PTR [rbp-0x28]
  4013c1:   add    rax,0x2c                 ; &Frame::Is_1_1, whose type is std::__n4861::suspend_never*.
  4013c5:   mov    rdi,rax                  ; Call suspend_never::await_resume() with this = &Frame::Is_1_1.
  4013c8:   call   401718 <std::__n4861::suspend_never::await_resume() const>
                                            ; suspend_never::await_resume does nothing.
  4013cd:   mov    rax,QWORD PTR [rbp-0x28]
  4013d1:   mov    rdx,QWORD PTR [rax+0x20] ; &Frame::continuation_out, whose type is std::__n4861::coroutine_handle<void>*.
  4013d5:   mov    rax,QWORD PTR [rbp-0x28]
  4013d9:   mov    QWORD PTR [rax+0x30],rdx ; Set Frame::a_1_2::hp_ to &Frame::continuation_out.
  4013dd:   mov    rax,QWORD PTR [rbp-0x28]
  4013e1:   mov    DWORD PTR [rax+0x38],0x0 ; Set Frame::i_2_3 to 0x0.
  4013e8:   mov    rax,QWORD PTR [rbp-0x28]
  4013ec:   add    rax,0x30                 ; &Frame::a_1_2, whose type is Awaiter.
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
  ; Call coroutine_handle::operator() with this = &Frame::_Coro_self_handle.
  401419:   mov    rdi,rax
  40141c:   call   40178e <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  ; Call Awaiter::await_suspend(coroutine_handle<void>) with this = &Frame::a_1_2, h = rax
  401421:   mov    rsi,rax
  401424:   mov    rdi,rbx
  401427:   call   401764 <Awaiter::await_suspend(std::__n4861::coroutine_handle<void>)>
  ; Return and don't free coroutine frame.
  40142c:   jmp    4014f4

  401431:   jmp    4014d0

  401436:   mov    rax,QWORD PTR [rbp-0x28]
  40143a:   add    rax,0x30                 ; &Frame::a_1_2, whose type is Awaiter*.
  40143e:   mov    rdi,rax                  ; Call Awaiter::await_resume() with this = &Frame::a_1_2.
  401441:   call   401782 <Awaiter::await_resume() const>
                                            ; The code equivalent to the following code has been omitted:
                                            ; std::cout << "counter: " << i << std::endl.
  40147a:   mov    eax,DWORD PTR [rax+0x38] ; Frame::i_2_3, whose type is unsigned int.
  40147d:   lea    edx,[rax+0x1]
  401480:   mov    rax,QWORD PTR [rbp-0x28]
  401484:   mov    DWORD PTR [rax+0x38],edx ; Frame:i_2_3 += 1
  401487:   jmp    4013e8                   ; Skip to the beginning of the for loop?

  40148c:   mov    rax,QWORD PTR [rbp-0x28]
  401490:   mov    WORD PTR [rax+0x28],0x6 ; Frame::_Coro_resume_index = 0x6.
  401496:   mov    rax,QWORD PTR [rbp-0x28]
  40149a:   lea    rbx,[rax+0x3c]          ; &Frame::Fs_1_5, whose type is std::__n4861::suspend_never*.
  40149e:   mov    rax,QWORD PTR [rbp-0x28]
  4014a2:   add    rax,0x18
  4014a6:   mov    rdi,rax
  4014a9:   call   40178e <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  4014ae:   mov    rsi,rax
  4014b1:   mov    rdi,rbx
  4014b4:   call   401708 <std::__n4861::suspend_never::await_suspend(std::__n4861::coroutine_handle<void>) const>
  4014b9:   jmp    4014f4                  ; Return and don't free coroutine frame.

  4014bb:   jmp    4014d0

  4014bd:   mov    rax,QWORD PTR [rbp-0x28]
  4014c1:   add    rax,0x3c ; &Frame::Fs_1_5, whose type is std::__n4861::suspend_never*.
  4014c5:   mov    rdi,rax  ; Call suspend_never::await_resume with this = &Frame::Fs_1_5.
  4014c8:   call   401718 <std::__n4861::suspend_never::await_resume() const>
  4014cd:   jmp    4014d0   ; 1. Free coroutine frame if Frame::_Coro_frame_needs_free is true.
                            ; 2. Return.

  4014cf:   nop
  4014d0:   mov    rax,QWORD PTR [rbp-0x28]
  4014d4:   movzx  eax,BYTE PTR [rax+0x2a]  ; Frame::_Coro_frame_needs_free
  4014d8:   movzx  eax,al                   ; AL is a part of AX.
  4014db:   test   eax,eax                  ; If Frame::_Coro_frame_needs_free is false,
  4014dd:   je     40158d                   ; then just return and do nothing.
  4014e3:   mov    rax,QWORD PTR [rbp-0x28] ; Else if Frame::_Coro_frame_needs_free is true,
  4014e7:   mov    rdi,rax                  ; then free coroutine frame,
  4014ea:   call   401060 <operator delete(void*)@plt>
  4014ef:   jmp    40158d                   ; and return.
  4014f4:   jmp    40158d

  4014f9:   mov    rdi,rax
  4014fc:   call   401030 <__cxa_begin_catch@plt>
  401501:   mov    rax,QWORD PTR [rbp-0x28]
  401505:   movzx  eax,BYTE PTR [rax+0x2b]
  401509:   xor    eax,0x1
  40150c:   test   al,al
  40150e:   je     401515 <counter(counter(std::__n4861::coroutine_handle<void>*)::_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame*) [clone .actor]+0x26c>
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
  40156f:   jne    40148c <counter(counter(std::__n4861::coroutine_handle<void>*)::_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame*) [clone .actor]+0x1e3>
  401575:   jmp    4014bd <counter(counter(std::__n4861::coroutine_handle<void>*)::_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame*) [clone .actor]+0x214>
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

# Reference

Assembly language:

+ [The 64 bit x86 C Calling Convention](https://aaronbloomfield.github.io/pdr/book/x86-64bit-ccc-chapter.pdf)
+ [x86 calling conventions](https://libdl.so/articles/x86_calling_conventions.html)
+ [Stack Overflow: What are the ESP and the EBP registers?](https://stackoverflow.com/questions/21718397/what-are-the-esp-and-the-ebp-registers)
+ [Stack Overflow: Why does the stack address grow towards decreasing memory addresses?](https://stackoverflow.com/questions/4560720/why-does-the-stack-address-grow-towards-decreasing-memory-addresses)
+ [Intel 64 and IA-32 Architectures Software Developer's Manual: Volume 2](https://www.intel.com/content/www/us/en/architecture-and-technology/64-ia-32-architectures-software-developer-instruction-set-reference-manual-325383.html)
+ [OSDev.org: CPU Registers x86](https://wiki.osdev.org/CPU_Registers_x86)
+ [Stack Overflow: Assembly language je jump function](https://stackoverflow.com/questions/1582960/assembly-language-je-jump-function)

Coroutine frame:

+ [Mircosoft, The Old New Thing: Debugging coroutine handles: The Microsoft Visual C++ compiler, clang, and gcc](https://devblogs.microsoft.com/oldnewthing/20211007-00/?p=105777)
+ [Clang 16.0.0: Debugging C++ Coroutines, coroutine frame](https://clang.llvm.org/docs/DebuggingCoroutines.html#coroutine-frame)
+ [gcc-mirror/gcc: C++ coroutines Initial implementation.](https://github.com/gcc-mirror/gcc/commit/49789fd08378e3ff7a6efd7c4f72b72654259b89)
+ [gcc-mirror/gcc: coroutines.cc]https://github.com/gcc-mirror/gcc/blob/2fa8c4a659a19ec971c80704f48f96c13aae9ac3/gcc/cp/coroutines.cc#L4336

https://jamespascoe.github.io/accu2022/#/Title-Slide
https://itnext.io/c-20-coroutines-complete-guide-7c3fc08db89d
