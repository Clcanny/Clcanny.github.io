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
                                     ; The callable object is of type std::coroutine_handle<>.
  401213:  mov    $0x40,%eax         ; Allocate 64 bytes.
  401218:  mov    %rax,%rdi          ; RDI is the first argument of operator new.
  40121b:  callq  401080 <_Znwm@plt> ; operator new(unsigned long)
  401220:  mov    %rax,-0x18(%rbp)   ; RAX is the result of operator new.
  401224:  mov    -0x18(%rbp),%rax   ; Memory layout is as follow:
; -------- 0x00
; 0x4012a9
; Start address of function counter(counter(std::__n4861::coroutine_handle<void>*)
; ::counter(std::__n4861::coroutine_handle<void>*).Frame*) [clone .actor].
counter(counter(std::__n4861::coroutine_handle<void>*)::counter(std::__n4861::coroutine_handle<void>*).Frame*) [clone .destroy]
; https://github.com/gcc-mirror/gcc/blob/master/gcc/cp/coroutines.cc
; https://github.com/gcc-mirror/gcc/blob/master/gcc/cp/coroutines.cc#L1449
; -------- 0x08
; 0x0      0x8      0x10     0x18       0x20      0x28
; |--------|--------|--------|--------   |--------|--
; |0x4012a9|0x401594|        |-0x28(%rbp)|        | 1
;                   |
;                   |
; The first argument of ReturnObject::promise_type::get_return_object().
  401228:  movb   $0x1,0x2a(%rax)
  40122c:  mov    -0x18(%rbp),%rax

  401230:  movq   $0x4012a9,(%rax)
  401237:  mov    -0x18(%rbp),%rax
  40123b:  movq   $0x401594,0x8(%rax)
  401243:  mov    -0x28(%rbp),%rdx
  401247:  mov    -0x18(%rbp),%rax
  40124b:  mov    %rdx,0x20(%rax)
  40124f:  mov    -0x18(%rbp),%rax
  401253:  add    $0x10,%rax
  401257:  mov    %rax,%rdi
  40125a:  callq  401718 <_ZN12ReturnObject12promise_type17get_return_objectEv>
  40125f:  mov    -0x18(%rbp),%rax
  401263:  movw   $0x0,0x28(%rax)
  401269:  mov    -0x18(%rbp),%rax
  40126d:  mov    %rax,%rdi
  401270:  callq  4012a9 <_Z7counterPZ7counterPNSt7__n486116coroutine_handleIvEEE50_Z7counterPNSt7__n486116coroutine_handleIvEE.Frame.actor>
  401275:  jmp    4012a3 <_Z7counterPNSt7__n486116coroutine_handleIvEE+0xad>
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

# Reference

+ [The 64 bit x86 C Calling Convention](https://aaronbloomfield.github.io/pdr/book/x86-64bit-ccc-chapter.pdf)
+ [x86 calling conventions](https://libdl.so/articles/x86_calling_conventions.html)
+ [Stack Overflow: What are the ESP and the EBP registers?](https://stackoverflow.com/questions/21718397/what-are-the-esp-and-the-ebp-registers)
+ [Stack Overflow: Why does the stack address grow towards decreasing memory addresses?](https://stackoverflow.com/questions/4560720/why-does-the-stack-address-grow-towards-decreasing-memory-addresses)
