---
title: useful-vim-plugin.md
date: 2020-06-14 05:01:26
categories:
  - [Computer Science, Tools, Vim]
---

# 常用的 VIM 插件

## 背景

VIM 有很多插件，但这些插件在笔者日常工作中都因为过于复杂而没有被充分利用；因而本篇文章着重介绍一些常用的插件及它们的精简命令。

## vim-easy-align

[junegunn/vim-easy-align](https://github.com/junegunn/vim-easy-align) 用于快速对齐。

测试文本如下：

```txt
# Command: todo
a & b &1 c
a1 && b1 && c1
```

### 惯用法

用 Shift-V 或 Ctrl-V 进入 Visual 模式，选中待对齐的文本区域，敲击 `:EasyAlign` 执行对齐命令。

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/useful-vim-plugin/start-easy-align.gif)

EasyAlign 的用法：`EasyAlign [position]/regexp/[options]`

regexp 采用与 VIM 相同的正则表达式语法

position 是可选项，默认值为 1 ，可选值有：1（第一个匹配正则表达式的分隔符）/ ... / -1（最后一个匹配正则表达式的分隔符）/ *（所有匹配正则表达式的分隔符）

常用的 options 如下：

|        名称         | 默认值 |                 可选项                 |                           描述                            |
| :-----------------: | :----: | :------------------------------------: | :-------------------------------------------------------: |
| **d**elimiter_align |   r    |     **l**eft **r**ight **c**enter      |                   决定分隔符的对齐方式                    |
|      **a**lign      |   l    |     **l**eft **r**ight **c**enter      | 决定分隔符左侧文本的对齐方式（除 position 是 * 的情况外） |
|   **i**ndentation   |   k    | **k**eep **d**eep **s**hallow **n**one |                         缩进模式                          |

options 有两种表达方式：

1. 类 JSON ：`{'delimiter_align': 'r', 'align': 'r'}`
2. 缩写：`[optionKey_1][optionValue_1][optionKey_2][optionValue_2]...`

由于类 JSON 表达式较长，笔者推荐缩写表达式，注意缩写表达式中不同的键值对之间不需要空格。

e.x. `EasyAlign */&[0-9&]\?/drar`

### delimiter_align 示例

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/useful-vim-plugin/delimiter-align-default.gif)

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/useful-vim-plugin/delimiter-align-left.gif)

### align 示例

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/useful-vim-plugin/align-default.gif)

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/useful-vim-plugin/align-right.gif)

### Markdown 表格示例

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/useful-vim-plugin/table-align.gif)
