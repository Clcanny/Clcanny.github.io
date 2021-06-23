---
title: A Simple Example of ANTLR4 and C++
date: 2020-09-13 15:00:00
categories:
  - [Computer Science, Programming Language, C++]
---
<!--more-->

# A Simple Example of ANTLR4 and C++

本篇文章着重介绍 C++ 下如何使用 ANTLR4 ，不会深究 ANTLR4 的语法。

## 定义语法文件

参考 [MySqlLexer.g4](https://github.com/antlr/grammars-v4/blob/master/sql/mysql/Positive-Technologies/MySqlLexer.g4) 和 [MySqlParser.g4](https://github.com/antlr/grammars-v4/blob/master/sql/mysql/Positive-Technologies/MySqlParser.g4) 定义一个非常简单的加减运算：

```g4
// ArithmeticLexer.g4
lexer grammar ArithmeticLexer;

options { language=Cpp; }

PLUS:        '+';
MINUS:       '-';
DEC_DIGIT:   [0-9]+;
```

```g4
// ArithmeticParser.g4
parser grammar ArithmeticParser;

options { tokenVocab=ArithmeticLexer; language=Cpp; }

expression
    : left=DEC_DIGIT PLUS  right=DEC_DIGIT
    | left=DEC_DIGIT MINUS right=DEC_DIGIT
    ;
```

```bash
# java -jar antlr-4.8-complete.jar ArithmeticLexer.g4 -Werror -o generated
# java -jar antlr-4.8-complete.jar ArithmeticParser.g4 -Werror -o generated
```

## 编译 ANTLR Cpp runtime

ANTLR4 不提供 Linux 下的二进制文件，需要从 [ANTLR4 源代码](https://github.com/antlr/antlr4) 自行编译。

编译依赖： `build-essential make cmake g++ git uuid-dev pkg-config`

```bash
cd antlr/runtime/Cpp
mkdir build && cd build
cmake ..
make -j20 && make install
```

编译头文件放于 `/usr/local/include/antlr4-runtime ` ，链接库放于 `/usr/local/lib` 。

若不想安装，也可执行 `make package` 命令将头文件和链接库打包到 `LIBANTLR4-4.8-Linux.tar.gz` 文件。

## 按 Listener 模式访问语法树

```cpp
#include "ANTLRInputStream.h"
#include "CommonTokenStream.h"
#include "generated/ArithmeticLexer.h"
#include "generated/ArithmeticParser.h"
#include "generated/ArithmeticParserBaseListener.h"
#include "tree/ParseTreeWalker.h"
#include <iostream>
#include <string>

class MyListener : public ArithmeticParserBaseListener {
 public:
    void exitExpression(ArithmeticParser::ExpressionContext* ctx) {
        int left = std::stoi(ctx->left->getText());
        int right = std::stoi(ctx->right->getText());
        if (ctx->PLUS() != nullptr) {
            std::cout << left + right << std::endl;
        } else {
            std::cout << left - right << std::endl;
        }
    }
};

int main() {
    antlr4::ANTLRInputStream inputStream("1+1");
    ArithmeticLexer lexer(&inputStream);
    antlr4::CommonTokenStream tokens(&lexer);
    ArithmeticParser parser(&tokens);
    MyListener listener;
    antlr4::tree::ParseTreeWalker::DEFAULT.walk(&listener, parser.expression());
    return 0;
}
```

```bash
g++ -std=c++11 main.cpp                                           \
    $(find generated -type f -name "*.cpp")                       \
    -I/usr/local/include/antlr4-runtime                           \
    -L/usr/local/lib/ -Wl,-rpath=/usr/local/lib/ -lantlr4-runtime \
    -o main
```

## Reference

+ https://github.com/antlr/antlr4/blob/master/doc/cpp-target.md
