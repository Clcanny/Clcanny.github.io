---
title: useful and easy new features of Cpp11
date: 2019-07-16 22:14:15
tags:
  - c++11
---

# 简单易用的 C++11 新特性

重构代码时提炼几点有用的 C++11 新特性，能够帮助大家写出更加优雅的 C++ 代码

## type cast

## move semantics

> 如何移动一头大象？在第二个冰箱中启动量子复制系统，克隆一只完全相同的大象，然后启动高能激光将第一个冰箱内的大象气化消失。

感谢[知乎](https://www.zhihu.com/question/22111546/answer/30801982)段子带来的快乐

### Value categories

> Each C++ expression is characterized by two independent properties: a *type* and a *value category*.

参考[Stroustrup 叙述 C++11 值类型取名历程](https://stackoverflow.com/questions/3601602/what-are-rvalues-lvalues-xvalues-glvalues-and-prvalues)，整理出判断值类型的表：

+ Has identity
  + It's possible to determine whether the expression refers to the same entity as another expression, such as by comparing addressses of the objects or the functions they identity (obtained directly or indirectly)
+ Can be moved from
  + Move constructor, move assignments operator, or another function overload that implements move semantics can bind to the expression.
  + The resource will not be used in another place or be discarded by explicitly.

|                     | has identity | hasn't identity |
| :-----------------: | :----------: | :-------------: |
|  can be moved from  |    xvalue    |     prvalue     |
| can't be moved from |    lvalue    |        -        |

glvaue (generalized lvalue) = xvalue + lvalue

rvalue = xvalue + prvalue

根据 [cppreference](https://en.cppreference.com/w/cpp/language/value_category) 的描述及实验，整理出值类型的属性：

|                                      | lvalue | xvalue | prvalue |
| :----------------------------------: | :----: | :----: | :-----: |
|                取地址                |   Y    |   N    |    N    |
|  出现在 built-in assignment 的左侧   |   Y    |   N    |    N    |
| polymorphic 静态类型与实际类型不一致 |   Y    |   Y    |    N    |
|    initialize a lvalue reference     |   Y    |   N    |    N    |
|    initialize an rvalue reference    |   N    |   Y    |    Y    |
| initialize a const lvalue reference  |   Y    |   Y    |    Y    |
|        绑定引用会延长生命周期        |   N    |   N    |    Y    |

根据值支持的操作也可以判断出值类型：

|              | 支持多态 | 不支持多态 |
| :----------: | :------: | :--------: |
| 不可以取地址 |  xvalue  |  prvalue   |
|  可以取地址  |  lvalue  |     -      |

### rvalue reference is a lvalue

> Each expression has some non-reference type, and each expression belongs to exactly one of the three primary value categories.

划重点：non-reference type, value category

不妨定义一个二元组 [non reference type, value category] 来描述表达式分类，取名为 full type

```cpp
#include <iostream>
using namespace std;

struct Test
{
    Test() = default;
    Test(Test& other) {
        cout << "copy constructor" << endl;
    }
    Test(Test&& other) {
        cout << "move constructor" << endl;
    }
};

int main()
{
    Test t1;
    Test&& r = std::move(t1);
    Test t2(r); // copy constructor

    Test t3(std::move(t1)); // move constructor
    Test t4(std::move(r)); // move constructor
}
```

以上代码来自 [SO](https://stackoverflow.com/questions/3601602/what-are-rvalues-lvalues-xvalues-glvalues-and-prvalues/9552880#9552880) ：如何解释 `Test t2(r)` 调用拷贝构造函数而不是移动构造函数？一种合理的解释如下：

|               |           type           | value category |
| :-----------: | :----------------------: | :------------: |
| std::move(t1) |           Test           |     rvalue     |
|       r       | rvalue reference of Test |     lvalue     |

full type 必须是 non reference type ，rvalue reference of Test 不满足定义，不妨直接删掉

|               |             type             | value category |
| :-----------: | :--------------------------: | :------------: |
| std::move(t1) |             Test             |     rvalue     |
|       r       | ~~rvalue reference of~~ Test |     rvalue     |

所以编译器选择拷贝构造函数而不是移动构造函数

```cpp
int main()
{
    Test t1;
    Test&& r1 = std::move(t1);
    Test&& r2 = std::move(r1);
    Test t2(r2); // copy constructor
}
```

类似地，编译器在决策 `t2(r3)` 调用哪一个构造函数的时候，也有一个类似的过程：

|               |             type             | value category |
| :-----------: | :--------------------------: | :------------: |
| std::move(t1) |             Test             |     rvalue     |
|      r1       | ~~rvalue reference of~~ Test |     lvalue     |
| std::move(r1) |             Test             |     rvalue     |
|      r2       | ~~rvalue reference of~~ Test |     rvalue     |

### Why rvalue reference can't be a rvalue?

```cpp
#include <algorithm>
#include <iostream>
#include <string>
using namespace std;

void UpperCaseInPlace(string& str)
{
    transform(str.begin(), str.end(), str.begin(), ::toupper);
}

bool compare(string& str)
{
    cout << "call lvalue version" << endl;
    string upperCaseStr(str);
    UpperCaseInPlace(upperCaseStr);
    return upperCaseStr == str;
}

bool compare(string&& str)
{
    cout << "call rvalue version" << endl;
    string upperCaseStr(str);
    UpperCaseInPlace(upperCaseStr);
    return upperCaseStr == str;
}

int main()
{
    string str = "a long string";
    compare(str);
    compare("a long string");
}
```

以上代码能够取得较优的性能：对于为右值的 string ，省去一次拷贝构造（省去一次 memcpy ）

聚焦于 compare 函数的 rvalue 版本：

```cpp
bool compare(string&& str)
{
    cout << "call rvalue version" << endl;
    string upperCaseStr(str);
    UpperCaseInPlace(upperCaseStr);
    return upperCaseStr == str;
}
```

假设推翻 C++11 的设计，右值引用也是右值，compare 函数的 rvalue 版本实现起来比较困难：期望通过拷贝一个右值引用得到一个全新的字符串 `upperCaseStr`

所以 C++11 现在的设计：**右值引用不是右值** 具备一定的合理性

### xvalue 如何产生？

1. a function call whose return type is rvalue reference to object, such as `std::move(x)`
2. `a[n]`, the built-in [subscript](https://en.cppreference.com/w/cpp/language/operator_member_access#Built-in_subscript_operator) expression, where one operand is an array rvalue
3. `a.m`, the [member of object](https://en.cppreference.com/w/cpp/language/operator_member_access#Built-in_member_access_operators) expression, where `a` is an rvalue and `m` is a non-static data member of non-reference type

根据以下两个性质可以判断表达式产生了 xvalue ：

1. 不可以取地址
2. 允许 upcast

```cpp
struct Super {};
struct Sub : public Super { int a; };
struct Test { Sub sub; };

// cannot take the address of an rvalue of type 'int'
// &((int[2]){1, 2}[0]);
Super&& a = ((Sub[1]){Sub()})[0];

// cannot take the address of an rvalue of type 'int'
// &(Sub().a);
Super&& b = Test().sub;

Sub c;
// cannot take the address of an rvalue of type 'Sub'
// &std::move(c);
Super&& rC = std::move(c);
```

注意：笔者认为 gcc 对右值的实现没有完全参照标准，请使用 clang 测试

```shell
clang++ --version
# clang version 7.0.1 (tags/RELEASE_701/final)
clang++ -std=c++11 test.cpp
```

### cheatsheet

> 来做场小测验吧！

|    a    | m (non-static data member) |  a.m   |
| :-----: | :------------------------: | :----: |
| lvalue  |       reference type       | lvalue |
| lvalue  |     non-reference type     | lvalue |
| xvalue  |       reference type       | lvalue |
| xvalue  |     non-reference type     | xvalue |
| prvalue |       reference type       | lvalue |
| prvalue |     non-reference type     | xvalue |

```cpp
#include <utility>

struct Super {};
struct Sub : public Super {};

Sub global;
struct TestNR { Sub sub; };
struct TestR { Sub &sub = global; };

int main()
{
    TestR tr;
    &(tr.sub);

    TestNR tnr;
    &(tnr.sub);

    &(std::move(TestR()).sub);

    // &(std::move(TestNR()).sub);
    static_cast<const Super&>(std::move(TestNR()).sub);

    &(TestR().sub);

    // &(TestNR().sub);
    static_cast<const Super&>(TestNR().sub);
}
```

|                         description                          | can  take address | can be move from | value category |
| :----------------------------------------------------------: | :---------------: | :--------------: | :------------: |
|             the name of a variable or a function             |         Y         |        N         |     lvalue     |
|    a function call whose return type is lvalue reference     |         Y         |        N         |     lvalue     |
| built-in [assignment and compound assignment](https://en.cppreference.com/w/cpp/language/operator_assignment) expressions |         Y         |        N         |     lvalue     |
| built-in [pre-increment and pre-decrement](https://en.cppreference.com/w/cpp/language/operator_incdec#Built-in_prefix_operators) expressions |         Y         |        N         |     lvalue     |
| a [string literal](https://en.cppreference.com/w/cpp/language/string_literal) |         Y         |        N         |     lvalue     |
| a.m except a is an rvalue and `m` is a non-static data member of non-reference type |                   |                  |     lvalue     |
|                                                              |                   |                  |                |
|                                                              |                   |                  |                |
|                                                              |                   |                  |                |

```cpp
int& id(int& x) { return x; }
int x = 1;
// a function call whose return type is lvalue reference
&id(x);
```

```cpp
int x;
// built-in assigment expression
bool equal = &(x = 1) == &x;
// equal is true
```

```cpp
// a string literal
&"string literal";
```



has identity 并不是一个优秀的判断原则，因为 has identity 说的是这个值原来是不是具名的

## copy elision

多返回值的最小代价 pair move + container move

pair copy elision + container move

## emplace ##

### 简单介绍

> Inserts a new element into the container constructed in-place with the given `args` if there is no element with the key in the container. The constructor of the new element (i.e. [std::pair](http://en.cppreference.com/w/cpp/utility/pair)<const Key, T>) is called with exactly the same arguments as supplied to `emplace`, forwarded via [std::forward](http://en.cppreference.com/w/cpp/utility/forward)<Args\>(args)…. The element may be constructed even if there already is an element with the key in the container, in which case the newly constructed element will be destroyed immediately.

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

<a name="#cheatsheet-function-call-return-lvalue-reference">call function returns lvalue reference</a> 