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

ReturnObject counter() {
  co_await std::suspend_always{};
  co_yield 0x12345678;
  co_yield 0x90ABCDEF;
  co_return 0x98765432;
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

```assembly
0000000000401212 <counter(counter()::_Z7counterv.Frame*) [clone .actor]>:
  401212:   push   rbp
  401213:   mov    rbp,rsp
  401216:   push   rbx
  401217:   sub    rsp,0x28
  40121b:   mov    QWORD PTR [rbp-0x28],rdi
  40121f:   mov    rax,QWORD PTR [rbp-0x28]
  401223:   movzx  eax,WORD PTR [rax+0x20]
  401227:   and    eax,0x1
  40122a:   test   ax,ax
  40122d:   je     40124d <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x3b>
  40122f:   mov    rax,QWORD PTR [rbp-0x28]
  401233:   movzx  eax,WORD PTR [rax+0x20]
  401237:   movzx  eax,ax
  40123a:   cmp    eax,0xb
  40123d:   ja     40124b <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x39>
  40123f:   mov    eax,eax
  401241:   mov    rax,QWORD PTR [rax*8+0x402008]
  401249:   jmp    rax
  40124b:   ud2
  40124d:   mov    rax,QWORD PTR [rbp-0x28]
  401251:   movzx  eax,WORD PTR [rax+0x20]
  401255:   movzx  eax,ax
  401258:   cmp    eax,0xa
  40125b:   ja     4012ad <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x9b>
  40125d:   mov    eax,eax
  40125f:   mov    rax,QWORD PTR [rax*8+0x402068]
  401267:   jmp    rax
  401269:   mov    rbx,QWORD PTR [rbp-0x28]
  40126d:   mov    rax,QWORD PTR [rbp-0x28]
  401271:   mov    rdi,rax
  401274:   call   401786 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::from_address(void*)>
  401279:   mov    QWORD PTR [rbx+0x18],rax
  40127d:   mov    rax,QWORD PTR [rbp-0x28]
  401281:   add    rax,0x10
  401285:   mov    rbx,QWORD PTR [rbp-0x28]
  401289:   mov    rdi,rax
  40128c:   call   4016ee <ReturnObject::promise_type::initial_suspend()>
  401291:   mov    BYTE PTR [rbx+0x23],al
  401294:   mov    rax,QWORD PTR [rbp-0x28]
  401298:   add    rax,0x23
  40129c:   mov    rdi,rax
  40129f:   call   4016a8 <std::__n4861::suspend_never::await_ready() const>
  4012a4:   xor    eax,0x1
  4012a7:   test   al,al
  4012a9:   jne    4012af <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x9d>
  4012ab:   jmp    4012e6 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0xd4>
  4012ad:   ud2
  4012af:   mov    rax,QWORD PTR [rbp-0x28]
  4012b3:   mov    WORD PTR [rax+0x20],0x2
  4012b9:   mov    rax,QWORD PTR [rbp-0x28]
  4012bd:   lea    rbx,[rax+0x23]
  4012c1:   mov    rax,QWORD PTR [rbp-0x28]
  4012c5:   add    rax,0x18
  4012c9:   mov    rdi,rax
  4012cc:   call   401764 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  4012d1:   mov    rsi,rax
  4012d4:   mov    rdi,rbx
  4012d7:   call   4016b8 <std::__n4861::suspend_never::await_suspend(std::__n4861::coroutine_handle<void>) const>
  4012dc:   jmp    4014f8 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2e6>
  4012e1:   jmp    4014db <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2c9>
  4012e6:   mov    rax,QWORD PTR [rbp-0x28]
  4012ea:   add    rax,0x23
  4012ee:   mov    rdi,rax
  4012f1:   call   4016c8 <std::__n4861::suspend_never::await_resume() const>
  4012f6:   mov    rax,QWORD PTR [rbp-0x28]
  4012fa:   add    rax,0x24
  4012fe:   mov    rdi,rax
  401301:   call   40167c <std::__n4861::suspend_always::await_ready() const>
  401306:   xor    eax,0x1
  401309:   test   al,al
  40130b:   je     401344 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x132>
  40130d:   mov    rax,QWORD PTR [rbp-0x28]
  401311:   mov    WORD PTR [rax+0x20],0x4
  401317:   mov    rax,QWORD PTR [rbp-0x28]
  40131b:   lea    rbx,[rax+0x24]
  40131f:   mov    rax,QWORD PTR [rbp-0x28]
  401323:   add    rax,0x18
  401327:   mov    rdi,rax
  40132a:   call   401764 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  40132f:   mov    rsi,rax
  401332:   mov    rdi,rbx
  401335:   call   40168c <std::__n4861::suspend_always::await_suspend(std::__n4861::coroutine_handle<void>) const>
  40133a:   jmp    4014f8 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2e6>
  40133f:   jmp    4014db <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2c9>
  401344:   mov    rax,QWORD PTR [rbp-0x28]
  401348:   add    rax,0x24
  40134c:   mov    rdi,rax
  40134f:   call   40169c <std::__n4861::suspend_always::await_resume() const>
  401354:   mov    rax,QWORD PTR [rbp-0x28]
  401358:   add    rax,0x10
  40135c:   mov    rbx,QWORD PTR [rbp-0x28]
  401360:   mov    esi,0x12345678
  401365:   mov    rdi,rax
  401368:   call   4016fe <ReturnObject::promise_type::yield_value(unsigned int)>
  40136d:   mov    BYTE PTR [rbx+0x25],al
  401370:   mov    rax,QWORD PTR [rbp-0x28]
  401374:   add    rax,0x25
  401378:   mov    rdi,rax
  40137b:   call   40167c <std::__n4861::suspend_always::await_ready() const>
  401380:   xor    eax,0x1
  401383:   test   al,al
  401385:   je     4013be <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x1ac>
  401387:   mov    rax,QWORD PTR [rbp-0x28]
  40138b:   mov    WORD PTR [rax+0x20],0x6
  401391:   mov    rax,QWORD PTR [rbp-0x28]
  401395:   lea    rbx,[rax+0x25]
  401399:   mov    rax,QWORD PTR [rbp-0x28]
  40139d:   add    rax,0x18
  4013a1:   mov    rdi,rax
  4013a4:   call   401764 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  4013a9:   mov    rsi,rax
  4013ac:   mov    rdi,rbx
  4013af:   call   40168c <std::__n4861::suspend_always::await_suspend(std::__n4861::coroutine_handle<void>) const>
  4013b4:   jmp    4014f8 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2e6>
  4013b9:   jmp    4014db <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2c9>
  4013be:   mov    rax,QWORD PTR [rbp-0x28]
  4013c2:   add    rax,0x25
  4013c6:   mov    rdi,rax
  4013c9:   call   40169c <std::__n4861::suspend_always::await_resume() const>
  4013ce:   mov    rax,QWORD PTR [rbp-0x28]
  4013d2:   add    rax,0x10
  4013d6:   mov    rbx,QWORD PTR [rbp-0x28]
  4013da:   mov    esi,0x90abcdef
  4013df:   mov    rdi,rax
  4013e2:   call   4016fe <ReturnObject::promise_type::yield_value(unsigned int)>
  4013e7:   mov    BYTE PTR [rbx+0x26],al
  4013ea:   mov    rax,QWORD PTR [rbp-0x28]
  4013ee:   add    rax,0x26
  4013f2:   mov    rdi,rax
  4013f5:   call   40167c <std::__n4861::suspend_always::await_ready() const>
  4013fa:   xor    eax,0x1
  4013fd:   test   al,al
  4013ff:   je     401438 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x226>
  401401:   mov    rax,QWORD PTR [rbp-0x28]
  401405:   mov    WORD PTR [rax+0x20],0x8
  40140b:   mov    rax,QWORD PTR [rbp-0x28]
  40140f:   lea    rbx,[rax+0x26]
  401413:   mov    rax,QWORD PTR [rbp-0x28]
  401417:   add    rax,0x18
  40141b:   mov    rdi,rax
  40141e:   call   401764 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  401423:   mov    rsi,rax
  401426:   mov    rdi,rbx
  401429:   call   40168c <std::__n4861::suspend_always::await_suspend(std::__n4861::coroutine_handle<void>) const>
  40142e:   jmp    4014f8 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2e6>
  401433:   jmp    4014db <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2c9>
  401438:   mov    rax,QWORD PTR [rbp-0x28]
  40143c:   add    rax,0x26
  401440:   mov    rdi,rax
  401443:   call   40169c <std::__n4861::suspend_always::await_resume() const>
  401448:   mov    rax,QWORD PTR [rbp-0x28]
  40144c:   add    rax,0x10
  401450:   mov    esi,0x98765432
  401455:   mov    rdi,rax
  401458:   call   40171a <ReturnObject::promise_type::return_value(unsigned int)>
  40145d:   nop
  40145e:   mov    rax,QWORD PTR [rbp-0x28]
  401462:   mov    QWORD PTR [rax],0x0
  401469:   mov    rax,QWORD PTR [rbp-0x28]
  40146d:   add    rax,0x10
  401471:   mov    rbx,QWORD PTR [rbp-0x28]
  401475:   mov    rdi,rax
  401478:   call   401732 <ReturnObject::promise_type::final_suspend()>
  40147d:   mov    BYTE PTR [rbx+0x27],al
  401480:   mov    rax,QWORD PTR [rbp-0x28]
  401484:   add    rax,0x27
  401488:   mov    rdi,rax
  40148b:   call   40167c <std::__n4861::suspend_always::await_ready() const>
  401490:   xor    eax,0x1
  401493:   test   al,al
  401495:   je     4014c8 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2b6>
  401497:   mov    rax,QWORD PTR [rbp-0x28]
  40149b:   mov    WORD PTR [rax+0x20],0xa
  4014a1:   mov    rax,QWORD PTR [rbp-0x28]
  4014a5:   lea    rbx,[rax+0x27]
  4014a9:   mov    rax,QWORD PTR [rbp-0x28]
  4014ad:   add    rax,0x18
  4014b1:   mov    rdi,rax
  4014b4:   call   401764 <std::__n4861::coroutine_handle<ReturnObject::promise_type>::operator std::__n4861::coroutine_handle<void>() const>
  4014b9:   mov    rsi,rax
  4014bc:   mov    rdi,rbx
  4014bf:   call   40168c <std::__n4861::suspend_always::await_suspend(std::__n4861::coroutine_handle<void>) const>
  4014c4:   jmp    4014f8 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2e6>
  4014c6:   jmp    4014db <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2c9>
  4014c8:   mov    rax,QWORD PTR [rbp-0x28]
  4014cc:   add    rax,0x27
  4014d0:   mov    rdi,rax
  4014d3:   call   40169c <std::__n4861::suspend_always::await_resume() const>
  4014d8:   jmp    4014db <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2c9>
  4014da:   nop
  4014db:   mov    rax,QWORD PTR [rbp-0x28]
  4014df:   movzx  eax,BYTE PTR [rax+0x22]
  4014e3:   movzx  eax,al
  4014e6:   test   eax,eax
  4014e8:   je     4014f8 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2e6>
  4014ea:   mov    rax,QWORD PTR [rbp-0x28]
  4014ee:   mov    rdi,rax
  4014f1:   call   401050 <operator delete(void*)@plt>
  4014f6:   jmp    4014f8 <counter(counter()::_Z7counterv.Frame*) [clone .actor]+0x2e6>
  4014f8:   nop
  4014f9:   mov    rbx,QWORD PTR [rbp-0x8]
  4014fd:   leave
  4014fe:   ret
```
