---
layout: post
title: "Hide Symbols Of Static Libraries"
date: 2020-12-16 11:07:26
categories:
  - dynamic linking
---

# 背景

在 [Dynamic Linking: Symbol Search Order](https://clcanny.github.io/2020/11/18/dynamic-linking-symbol-search-order/#A-coredump) 中介绍了由动态链接库加载顺序和符号查找顺序不一致导致的 coredump ，导致问题的根本原因是违反了 One Definition Rule ；但大型软件的依赖关系非常复杂，重复引入同一个链接库是不可避免的。

如果三方库提供了静态链接库，重复引入链接库导致违反 One Definition Rule 的问题可以被解决。

## 复现

```cpp
// main.cpp
int main() {}
```

```cpp
// a.cpp
void accessVar();
class A {
 public:
  A() {
    accessVar();
  }
} _;
```

```cpp
// b.cpp
void accessVar();
class B {
 public:
  B() {
    accessVar();
  }
} _;
```

```makefile
# Makefile
all :
        g++ e.cpp -std=c++11 -c -fPIC -o e.o
        ar -rc libe.a e.o
        g++ a.cpp -std=c++11 -shared -fPIC -L$(PWD) -l:libe.a -o liba.so
        g++ b.cpp -std=c++11 -shared -fPIC -L$(PWD) -l:libe.a -o libb.so
        g++ main.cpp -std=c++11 -L$(PWD) -Wl,-rpath=$(PWD) -la -lb -o main
```

# Shadow static library

## Use --exclude-libs

# 参考资料

+ [Stack Overflow: How to apply -fvisibility option to symbols in static libraries?](https://stackoverflow.com/questions/2222162/how-to-apply-fvisibility-option-to-symbols-in-static-libraries)
+ [Free the Software!: Re: hiding of (global) C++ symbols in shared object](https://sourceware.org/legacy-ml/binutils/2000-05/msg00305.html)
