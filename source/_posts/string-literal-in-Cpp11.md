---
title: string literal in Cpp11
date: 2020-02-16 22:38:00
tags:
  - c++11
---
<!--more-->

# 在 C++ 中优雅地写多行字符串

## 背景

在 UT 中常常碰到以下需求：

```cpp
TEST_F(TestSuite, deserialize) {
  auto jsonStr = "{\"name\":\"James\",\"nickname\":\"goodboy\"}";
  auto object = deserialze(jsonStr);
}
```

`jsonStr` 不直观，我们想要 json 原本的样子

## String Literal

C++11 提供了 `R"delimiter(raw string)delimiter"` 的语法，其中 `delimiter` 可以自行定义

有了 String Literal ，以上代码可以写成：

```cpp
R"delimiter(
{
  "name": "James",
  "nickname": "good boy"
}
)delimiter"
```

但我们往往需要同时兼顾代码的对齐以及字符串的格式（比如将字符串打印出来），比如：

```cpp
#include <iostream>

int main() {
    auto s = R"delimiter(
        {
          "name": "James",
          "nickname": "good boy"
        }
        )delimiter";
    std::cout << s << std::endl;
}
```

```bash

        {
          "name": "James",
          "nickname": "good boy"
        }

```

空行和行首的空格是为了对齐代码而引入的，我们并不希望它们也打印出来，符合期望的输出是：

```cpp
{
  "name": "James",
  "nickname": "good boy"
}
```

## Trim

为减少性能消耗，Trim 需要在编译期完成

有两种方法做到这一点：

1. 模板：将字符串作为模板参数传入
2. constexpr

模板被证明是行不通的，将在函数内声明的字符串字面量作为模板参数传给模板类会报错：`non-type template argument refers to object that does not have linkage`

```cpp
template <int N>
class StringLiteral {
 private:
    char mArray[N];

 public:
    template <int S>
    constexpr StringLiteral(const char (&s)[S],
                            bool omitFirstEmptyLine,
                            bool omitLastEmptyLine) {
        static_assert(S >= 1, "");

        int begin = 0;
        // Omit the first empty line.
        if (omitFirstEmptyLine && s[0] == '\n') {
            begin = 1;
        }
        // Omit the last empty line.
        // N-2 N-1 N
        // \n  \0
        int end = N;
        if (omitLastEmptyLine && s[N - 2] == '\n') {
            end = N - 1;
        }

        int minSpaceNum = N;
        bool newLine = true;
        int spaceNum = 0;
        for (int i = begin; i < end; i++) {
            if (s[i] == '\n' || i == end - 1) {
                if (minSpaceNum > spaceNum) {
                    minSpaceNum = spaceNum;
                }
                newLine = true;
                spaceNum = 0;
                continue;
            }
            if (s[i] == ' ' && newLine) {
                spaceNum++;
                continue;
            }
            newLine = false;
        }

        int k = 0;
        spaceNum = 0;
        for (int i = begin; i < end - 1; i++) {
            if (s[i] == '\n') {
                spaceNum = 0;
                mArray[k] = s[i];
                k++;
                continue;
            }
            if (spaceNum < minSpaceNum) {
                spaceNum++;
                continue;
            }
            mArray[k] = s[i];
            k++;
        }
        mArray[k] = '\0';

        // Omit the last empty line.
        if (omitLastEmptyLine && mArray[k - 1] == '\n') {
            mArray[k - 1] = '\0';
        }
    }

    constexpr const char* c_str() const {
        return mArray;
    }
};

template <int N>
constexpr auto literal(const char (&lit)[N]) -> StringLiteral<N> {
    return StringLiteral<N>(lit, true, true);
}
```

## 编译

由于使用了 constexpr 特性，需要在 c++14 标准下编译

```bash
clang++ -std=c++14 -O0 -ggdb test.cpp -o test
```

## 测试

```cpp
int main() {
    static constexpr auto a = literal(R"delimiter(
        test
        test
        )delimiter");
    static constexpr auto b = literal(R"delimiter(
test
test
)delimiter");
    static constexpr auto c = literal(R"delimiter(
        test
test
)delimiter");
    static constexpr auto d = literal(R"delimiter(
                test
        test
        )delimiter");
    static constexpr auto s = d.c_str();
    std::cout << a.c_str() << std::endl;
    std::cout << b.c_str() << std::endl;
    std::cout << c.c_str() << std::endl;
    std::cout << s << std::endl;
}
```

```cpp
int main() {
    static constexpr auto s = literal(R"delimiter(
        {
          "name": "James",
          "nickname": "good boy"
        }
        )delimiter");
    std::cout << s.c_str() << std::endl;
}
```

输出：

```bash
{
  "name": "James",
  "nickname": "good boy"
}
```

# Reference

1. [string literal](https://en.cppreference.com/w/cpp/language/string_literal)
2. [Compile-time string concatenation](https://akrzemi1.wordpress.com/2017/06/28/compile-time-string-concatenation/)
3. [C-Style Strings as template arguments?](https://stackoverflow.com/questions/1826464/c-style-strings-as-template-arguments)

