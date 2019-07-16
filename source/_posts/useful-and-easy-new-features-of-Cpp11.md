---
title: useful and easy new features of Cpp11
date: 2019-07-16 22:14:15
tags:
  - c++11
---

# 简单易用的 C++11 新特性

重构代码时提炼几点有用的 C++11 新特性，能够帮助大家写出更加优雅的 C++ 代码

## emplace ##

### 简单介绍

> Inserts a new element into the container constructed in-place with the given `args` if there is no element with the key in the container. The constructor of the new element (i.e. [std::pair](http://en.cppreference.com/w/cpp/utility/pair)\<const Key, T\>) is called with exactly the same arguments as supplied to `emplace`, forwarded via [std::forward](http://en.cppreference.com/w/cpp/utility/forward)\<Args\>(args)…. The element may be constructed even if there already is an element with the key in the container, in which case the newly constructed element will be destroyed immediately.

引用自 [cppreference](https://en.cppreference.com/w/cpp/container/map/emplace) 的这段话可以归纳为三点：

1. 原地构造
2. 完美转发
3. 即使元素存在也可能引发一次不必要的构造

考虑下面一个禁止任何拷贝的类：

```cpp
struct Test
{
    Test(int, int) {};
    Test(const Test& other) = delete;
    Test(Test&& other) = delete;
    Test& operator=(const Test& other) = delete;
    Test& operator=(Test&& other) = delete;
};
```

在 c++11 之前如何为 `map<int, Test> m` 插入元素呢？

```cpp
// error: use of deleted function Test::Test(const Test&)
// template argument deduction/substitution failed
m.insert(std::make_pair(1, Test(1, 1)));
```

```cpp
// error: use of deleted function ‘Test& Test::operator=(Test&&)
// error: no matching function for call to Test::Test()
m[1] = Test(1, 1);
```

笔者没有想到不 workaround 的办法：为 Test 类增加默认构造函数，放开移动拷贝构造函数的限制等

在 emplace 之后，你可以这么做：

```cpp
m.emplace(
  std::piecewise_construct,
  std::forward_as_tuple(1), // 构造 key 用到的参数
  std::forward_as_tuple(1, 1)); // 构造 value 用到的参数
```

### 其它形式的 emplace

```cpp
map<string, string> m;
// uses pair's move constructor
m.emplace(make_pair(string("a"), string("a")));
// uses pair's converting move constructor
m.emplace(make_pair("a", "a"));
// uses pair's template constructor
m.emplace("a", "a");
```

如果 key 和 value 都是单参数构造函数且具备隐式转换，emplace 用起来最方便

### 实际用途

在 C++11 之前，为避免多次构造，往容器里塞元素要这么写：

```cpp
vector<Element> v;
v.push_back(Element()); // 提供一个非常轻量的无参数构造函数
Element& e = v.back();
e.field = 1;
// 其它赋值操作
```

这段代码是不优雅的：提供专门为容器准备的无参数构造函数、第一次看非常困惑

利用 emplace 之后：

```cpp
vector<Element> v;
v.emplace_back(1, 2, 3);
```

代码变得更直观，且性能没有下降，甚至还减少一次对无参数构造函数的调用

### emplace 是如何工作的？

```cpp
template <class _Tp, class _Allocator>
template <class... _Args>
void vector<_Tp, _Allocator>::emplace_back(_Args&&... __args)
{
  // omit the relation between capacity and size
  __RAII_IncreaseAnnotator __annotator(*this);
  __alloc_traits::construct(this->__alloc(),
                            _VSTD::__to_raw_pointer(this->__end_),
                            _VSTD::forward<_Args>(__args)...);
  __annotator.__done();
}

using __alloc_traits = allocator_traits<_Allocator>;
```

根据 [cppreference](https://en.cppreference.com/w/cpp/memory/allocator/construct) 的描述，`std::allocator<T>::construct` 的作用是

> Constructs an object of type `T` in allocated uninitialized storage pointed to by `p`, using placement-new

Calls `::new((void *)p) U([std::forward]<Args>(args)…)`

一般而言，分配内存与构建对象是绑定的，而 placement new 只负责在已分配的内存上构建对象

利用 placement new 和完美转发，emplace 的实现顺理成章：

```cpp
template <typename E>
struct UniVec
{
    uint8_t mElement[sizeof(E)];

    template <class... Args>
    void emplace_back(Args&&... args)
    {
        new (static_cast<void*>(mElement)) E(forward<Args>(args)...);
    }

    E* begin()
    {
        return reinterpret_cast<E*>(mElement);
    }
};
```

`UniVec` 是一个最多只能存放一个元素的 Vector ，`emplace_back` 的实现是使用完美转发的参数调用 `placement new`

```cpp
struct Test
{
    Test(int a, int b)
        : mA(a)
        , mB(b)
    {}

    Test(const Test& other) = delete;
    Test(Test&& other) = delete;
    Test& operator=(const Test& other) = delete;
    Test& operator=(Test&& other) = delete;

    int mA;
    int mB;
};

int main()
{
    UniVec<Test> v;
    v.emplace_back<int, int>(1, 1);
    cout << v.begin()->mA << endl;
    cout << v.begin()->mB << endl;
}
```

以上程序能正常编译运行，说明 emplace_back 确实如预期运行

## 编译期反射 + static_assert = concept

concept $\approx$ 接口

```cpp
template <typename Engine>
class EngineWrapper
{
    using R = typename concepts::Get_Caller_MethodRT0<Engine>::type;

    static_assert(
        concepts::IsStandardRandom<Engine>() ||
        concepts::IsMonkeyRandom<Engine>(),
        "Engine should be a standard random or monkey random");
}
```

## Cast

