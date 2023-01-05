---
layout: post
title: Callback To C++20 Coroutine
date: 2023-01-03 15:35:11
categories:
  - [Computer Science, Programming Language, C++]
---

```cpp
// g++ -std=c++20 -fcoroutines -ggdb -O0 main.cc -o main.o
#include <coroutine>
#include <functional>
#include <iostream>

void thirdFunc(int i, const std::function<void(int j)>& callback) {
  callback(i + 1);
}

auto thirdFunc2Co(int i) {
  struct awaiter : std::suspend_always {
    explicit awaiter(int i): i_(i), j_(0) {}
    void await_suspend(std::coroutine_handle<> handle) {
      thirdFunc(i_, [this, handle](int j) { j_ = j; handle(); });
    }
    int await_resume() { return j_; }
    int i_, j_;
  };
  return awaiter(i);
}

struct ReturnObject {
  struct promise_type {
    ReturnObject get_return_object() {
      return {
        .h_ = std::coroutine_handle<promise_type>::from_promise(*this)
      };
    }
    std::suspend_never initial_suspend() { return {}; }
    std::suspend_always yield_value(unsigned int value) {
      value_ = value;
      return {};
    }
    void return_value(unsigned int value) {
      value_ = value;
    }
    std::suspend_always final_suspend() noexcept { return {}; }
    void unhandled_exception() {}
    unsigned int value_;
  };
  std::coroutine_handle<promise_type> h_;
};

ReturnObject counter() {
  int j = co_await thirdFunc2Co(1);
  co_return j;
}

int main() {
  auto h = counter().h_;
  auto& promise = h.promise();
  std::cout << promise.value_ << std::endl;
  h.destroy();
  return 0;
}
```

# Reference

+ [Stack Overflow: Turning a function call which takes a callback into a coroutine](https://stackoverflow.com/questions/64270626/turning-a-function-call-which-takes-a-callback-into-a-coroutine)
