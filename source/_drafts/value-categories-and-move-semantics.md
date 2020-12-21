---
layout: post
title: "Value Categories And Move Semantics"
date: 2020-12-13 15:05:18
tags:
  - cplusplus
---

# Value categories

## Primary categories

> There were only two independent properties of values:

+ Has identity
  + It's possible to determine whether the expression refers to the same entity as another expression, such as by comparing addressses of the objects or the functions they identity (obtained directly or indirectly).
+ Can be moved from
  + Move constructor, move assignments operator, or another function overload that implements move semantics can bind to the expression.
  + The resource will not be used in another place or be discarded by explicitly.

|                     | has identity | hasn't identity |
| :-----------------: | :----------: | :-------------: |
|  can be moved from  |    xvalue    |     prvalue     |
| can't be moved from |    lvalue    |        -        |

根据 [cppreference](https://en.cppreference.com/w/cpp/language/value_category) 的描述，整理出值类型的属性：

|                                      | lvalue | xvalue | prvalue |
| :----------------------------------: | :----: | :----: | :-----: |
|                取地址                |   Y    |   N    |    N    |
|  出现在 built-in assignment 的左侧   |   Y    |   N    |    N    |
| polymorphic 静态类型与实际类型不一致 |   Y    |   Y    |    N    |
|    initialize a lvalue reference     |   Y    |   N    |    N    |
|    initialize an rvalue reference    |   N    |   Y    |    Y    |
| initialize a const lvalue reference  |   Y    |   Y    |    Y    |
|        绑定引用会延长生命周期        |   N    |   N    |    Y    |

## Mixed categories

1. glvaue (generalized lvalue) = xvalue + lvalue
2. rvalue = xvalue + prvalue

## Play with categories

#### Compiler is a liar

##### prvalue 不支持多态？

[What is an example of a difference in allowed usage or behavior between an xvalue and a prvalue FOR NON-POD objects?](https://stackoverflow.com/questions/15482508/what-is-an-example-of-a-difference-in-allowed-usage-or-behavior-between-an-xvalu) 对 **prvalue 不支持多态** 有一个看似合理的解释：

> Correspondingly, because a prvalue's static type is guaranteed to be its dynamic type, extending its lifetime is meaningful and can be done by the compiler. On the other hand, for the xvalue, the object is at some unknown, arbitrary location, so the compiler couldn't easily extend its lifetime, especially given that the type could be polymorphic.

延长 prvalue 需要确保编译器看到的类型（静态类型）是对象的真实类型（动态类型），否则编译器不知道该如何回收栈空间

![polymorphic-of-prvalue-reference](https://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/useful-and-easy-new-features-of-Cpp11/polymorphic-of-prvalue-reference.jpg)

prvalue reference 延长 prvalue 生命周期在 clang7 的实现方式：

1. 临时变量转正：栈顶指针在函数调用后移动到返回值之上（更低的地址）
2. 使用多态指针指向转正后的临时变量

至少在 clang 7 的实现方式下，prvalue 是可以使用多态的

严格意义上说，编译器应该在编译期拒绝 polymorphic prvalue reference ，以符合标准

标准没有规定引用必须实现成指针，因而上图斜上方的实现方法在 prvalue 的场景下也是可行的，但这种实现方法就必须拒绝 polymorphic prvalue reference ，否则运行期会出现非预期的行为

##### rvalue 不能出现在赋值表达式的左侧？

xvalue 是具名变量，出现在赋值表达式左侧是可以理解的，那么 prvalue 呢？

```shell
clang version 8.0.1-svn363027-1~exp1~20190611210016.75 (branches/release_80)
Target: x86_64-pc-linux-gnu
Thread model: posix
InstalledDir: /usr/bin
```

```cpp
// clang++-8 -std=c++11 -emit-llvm -S prvalue.cpp
struct Test { virtual void f() {} };
Test Make() {
    return Test();
}
int main() {
    Make() = Test();
}
```

```ll
define dso_local i32 @main() #2 {
  %1 = alloca %struct.Test, align 8
  %2 = alloca %struct.Test, align 8
  %3 = bitcast %struct.Test* %1 to i8*
  call void @llvm.memset.p0i8.i64(i8* align 8 %3, i8 0, i64 8, i1 false)
  call void @_ZN4TestC2Ev(%struct.Test* %1) #3
  call void @_Z4Makev(%struct.Test* sret %2)
  %4 = call %struct.Test* @_ZN4TestaSEOS_(%struct.Test* %2, %struct.Test* %1) #3
  ret i32 0
}
```

笔者稍稍修改 `main` 函数，去除掉对理解没有帮助的修饰符 `dereferenceable`

![prvalue-left-operand](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/useful-and-easy-new-features-of-Cpp11/prvalue-left-operand.png)

Clang8 并没有立即消除本应该失去生命周期的变量，因而 prvalue 可以被赋值

再看以下一段更加直观的代码：

```cpp
include <iostream>
using namespace std;
struct Test
{
    Test() = default;
    Test(const Test&) = default;
    virtual ~Test() {
        cout << "~Test()" << endl;
    }
    Test& operator=(Test&& other) {
        cout << "operator=" << endl;
        return *this;
    }
};
Test Make() {
    return Test();
}
int main() {
    Make() = Test();
}
```

输出：

```shell
operator=
~Test()
~Test()
```

在为 prvalue 赋值的场景下，Clang 8 延长了临时变量的生命周期至函数结束

但对于基础类型（如 `int` ），其右值仍然不可出现在辅助表达式左侧（这是编译器的一个谎言）

如果自行实现一个严格控制变量声明周期的编译器，`prvalue` 则不能出现在赋值表达式左侧

#### Some specific rules

##### rvalue reference is a lvalue

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

full type 必须是 non reference type ，rvalue reference of Test 不满足定义，不妨直接删掉 reference 部分

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

类似地，编译器在决策 `t2(r2)` 调用哪一个构造函数的时候，也有一个类似的过程：

|               |             type             | value category |
| :-----------: | :--------------------------: | :------------: |
| std::move(t1) |             Test             |     rvalue     |
|      r1       | ~~rvalue reference of~~ Test |     lvalue     |
| std::move(r1) |             Test             |     rvalue     |
|      r2       | ~~rvalue reference of~~ Test |     rvalue     |

###### Why rvalue reference can't be a rvalue?

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

所以 C++11 现在的设计：**右值引用不是右值**具备一定的合理性

##### value category of function return value isn't value category of function call

| value category of function return value | value catrgory of function call |
| :-------------------------------------: | :-----------------------------: |
|            lvalue reference             |             lvalue              |
|      rvalue reference to function       |             lvalue              |
|       rvalue reference to object        |             xvalue              |
|              non-reference              |             rvalue              |

#### Why we need xvalue ?

[SO](https://stackoverflow.com/questions/3601602/what-are-rvalues-lvalues-xvalues-glvalues-and-prvalues/9552880#9552880) 的回答认为 xvalue 和 prvalue 的最大差别是 xvalue 可以出现在赋值表达式左侧而 prvalue 不可以，然而笔者认为这个说法是错的：

1. [cppreference](https://en.cppreference.com/w/cpp/language/value_category) 明确提到：An rvalue can't be used as the left-hand operand of the built-in assignment or compound assignment operators. xvalue 和 prvalue 按照标准都不允许出现在赋值表达式的左侧
2. 在 **Compiler is a liar** 一节讨论过 Clang 对非基础类型的 rvalue 出现在赋值表达式左侧的处理方式，非基础类型的 xvalue 和 prvalue 都可以出现在赋值表达式的左侧

需要 xvalue 的原因是它既有名字又可以移动，既不是 lvalue 又不是 prvalue

#### xvalue 如何产生？

1. a function call whose return type is rvalue reference to object, such as `std::move(x)`
2. `a[n]`, the built-in [subscript](https://en.cppreference.com/w/cpp/language/operator_member_access#Built-in_subscript_operator) expression, where one operand is an array rvalue
3. `a.m`, the [member of object](https://en.cppreference.com/w/cpp/language/operator_member_access#Built-in_member_access_operators) expression, where `a` is an rvalue and `m` is a non-static data member of non-reference type

|      |                         has identity                         |              can be move from               | value category |
| :--: | :----------------------------------------------------------: | :-----------------------------------------: | :------------: |
|  1   | 看上去 function call 没有 identity <br>但函数返回的引用一般来自函数实参或全局变量<br>Y | Y<br>返回右值引用的目的是使得调用者获得右值 |     xvalue     |
|  2   |                      n 是 identity<br>Y                      |             Y<br>为什么可移动？             |     xvalue     |
|  3   |                      m 是 identity<br>Y                      |             Y<br>为什么可移动？             |     xvalue     |

```cpp
struct Super {};
struct Sub : public Super { int a; };
struct Test { Sub sub; };

// cannot take the address of an rvalue of type 'Sub'
// &((Sub[2]){Sub(), Sub()}[0]);
Super&& a = ((Sub[1]){Sub()})[0];

// cannot take the address of an rvalue of type 'int'
// &(Sub().a);
Super&& b = Test().sub;

Sub c;
// cannot take the address of an rvalue of type 'Sub'
// &std::move(c);
Super&& rC = std::move(c);
```

为什么 `a[n]` 和 `a.m` 可移动？

> 女朋友常说：”你是我的，所以你的钱也是我的“

```cpp
struct Money {};
struct Person { Money m };
Person you;
Person ry&& = std::move(you);
Person yourGirlFriend;
// you.money 是一个 xvalue
youGirlFried.money = you.money;
```

```cpp
Person getGoodMan() { return Person; }
Person girlFriend;
grilFriend.money = getGoodMan.money
```

> ”你的钱，我要了“

### copy constructor & move constructor

左值匹配拷贝构造函数，右值匹配移动构造函数

识别左值右值的时候注意两条规则：

1. rvalue reference 会被当做 lvalue 处理
2. 函数调用的值类型不等于函数返回值的值类型

### perfect forward

```cpp
#include <iostream>
#include <utility>
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

void f(Test& t)
{
    Test t2(t);
}

void f(Test&& t)
{
    Test t2(move(t));
}

template <typename T>
void g(T&& t)
{
    Test t2(forward<T>(t));
}

int main()
{
    Test t;
    f(t);
    f(move(t));
    g(t);
    g(move(t));
}
```

代码输出：

```shell
#include <iostream>
#include <utility>
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

void f(Test& t)
{
    Test t2(t);
}

void f(Test&& t)
{
    Test t2(move(t));
}

template <typename T>
void g(T&& t)
{
    Test t2(forward<T>(t));
}

int main()
{
    Test t;
    f(t);
    f(move(t));
    g(t);
    g(move(t));
}
```

代码输出：

```shell
copy constructor
move constructor
copy constructor
move constructor
```

函数 `g` 调用的 `forward` 函数即是完美转发，完美转发保证将左值引用当做左值处理，将右值引用当做右值处理

函数 g 的参数类型是 `T&&` ，笔者认为 `&&` 在这里并不代表右值，而是代表 universal reference

`T&&` 不是右值，是 universal reference （这是 C++11 的另外一个大坑）

### 右值语义如何影响代码

在不考虑 copy elision 的情况下（编译时添加 `-fno-elide-constructors` 选项），右值语义可以大大减小返回复杂类型的成本

```cpp
void f(vector<int>* output);
```

```cpp
vector<int> g() {
  vector<int> x = {1, 2, 3};
  return x;
}
```

函数 `f` 和 函数 `g` 的性能差距即使在不考虑 copy elision 的情况下，也是非常小的，而函数 `g` 的含义却比函数 `f` 的含义要清晰

顺带提一句：调用"返回值不是引用类型的函数"的表达式的值类型是右值，代码不必写成 `std::move(x)` 的形式

两个返回值的函数可以写成如下形式：

```cpp
// clang++-8 -std=c++11 -fno-elide-constructors test.cpp
#include <utility>
#include <vector>
using namespace std;

struct Vec
{
    Vec() = default;
    Vec(Vec& other) = delete;
    Vec(Vec&& other) = default;
};

template <typename T, typename U>
struct Pair
{
    Pair(T&& t, U&& u) : first(forward<T>(t)), second(forward<U>(u)) {}
    Pair(Pair& other) = delete;
    Pair(Pair&& other) : first(move(other.first)), second(move(other.second)) {}

    T first;
    U second;
};

bool f(Vec* v)
{
}

Pair<bool, Vec> g()
{
    Vec v;
    return Pair<bool, Vec>(true, move(v));
}

int main()
{
    Pair<bool, Vec> result(g());
}
```

相较于函数 `f` ，函数 `g` 最多多调用两次移动构造函数

# copy elision

1. Return Value Optimization = RVO
2. Named Return Value Optimization = NRVO

在 C++11 ，标准只是允许 `copy elision` 而不是强制 `copy elision` ，不过 `copy elision` 在主流编译器已经得到实现。

## 触发 NRVO 的条件

返回相同的具名变量。

## Guaranteed copy elision

|                 |                              gcc                               |                    clang                    |
| :-------------: | :------------------------------------------------------------: | :-----------------------------------------: |
| support version | [7](https://www.gnu.org/software/gcc/projects/cxx-status.html) | [4](https://clang.llvm.org/cxx_status.html) |

guaranteed copy elision 由 [Wording for guaranteed copy elision through simplified value categories](http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2016/p0135r1.html) 提出，在 C++17 可以使用。

不过在 Guaranteed copy elision 下，临时变量和 prvalue (?) 的语义发生了变化。

# 参考资料

+ [知乎：如何评价 C++11 的右值引用（Rvalue reference）特性？](https://www.zhihu.com/question/22111546/answer/30801982)
+ [Stack Overflow: What are rvalues, lvalues, xvalues, glvalues, and prvalues?](https://stackoverflow.com/questions/3601602/what-are-rvalues-lvalues-xvalues-glvalues-and-prvalues)
+ [Stack Overflow: Empirically determine value category of C++11 expression?](https://stackoverflow.com/questions/16637945/empirically-determine-value-category-of-c11-expression/16638081#16638081)
+ [Bjarne Stroustrup: "New" Value Terminology](https://www.stroustrup.com/terminology.pdf)
+ [C++ reference: Value categories](https://en.cppreference.com/w/cpp/language/value_category)
+ [Stack Overflow: What is an example of a difference in allowed usage or behavior between an xvalue and a prvalue FOR NON-POD objects?](https://stackoverflow.com/questions/15482508/what-is-an-example-of-a-difference-in-allowed-usage-or-behavior-between-an-xvalu)
+ [Open Standards: Wording for guaranteed copy elision through simplified value categories](http://www.open-std.org/jtc1/sc22/wg21/docs/papers/2016/p0135r1.html)
+ [Medium: Value Categories in C++17](https://medium.com/@barryrevzin/value-categories-in-c-17-f56ae54bccbe)
+ [Sutter’s Mill: GotW #88: A Candidate For the "Most Important const"](https://herbsutter.com/2008/01/01/gotw-88-a-candidate-for-the-most-important-const/)
