---
layout: draft
title: "Columnar Storage: Dremel"
date: 2021-03-29 16:31:00
tags:
  - columnar storage
---

# Repetition and Definition Levels

```gRPC
message Document {
    required int64 DocId;
    optional group Links {
        repeated int64 Backward;
        repeated int64 Forward;
    }
    repeated group Name {
        repeated group Language {
            required string Code;
            optional string Country;
        }
        optional string url;
    }
}
```

```text
# r1
DocId: 10
Links
    Forward: 20
    Forward: 40
    Forward: 60
Name
    Language
        Code: 'en-us'
        Country: 'us'
    Language
        Code: 'en'
    Url: 'http://A'
Name
    Url: 'http://B'
Name
    Language
        Code: 'en-gb'
        Country: 'gb'
```

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/columnar-storage-dremel/r1.png)

```text
# r2
DocId: 20
Links
    Backward: 10
    Backward: 30
    Backward: 80
Name
    Url: 'http://C'
```

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/columnar-storage-dremel/r2.png)

## Repetition Level

> It tells us at what repeated field in the field’s path the value has repeated.

在 Repetition Level 小节，我们会使用 \[\] 和矩形表达 repeated 字段，**不包括** optional 字段（注意与 Definition Level 小节区分）。

### Name.Language.Code

论文以 Name.Language.Code 为例子解释了 repetition level ：

> Now suppose we are scanning record r1 top down.
> When we encounter 'en-us', we have not seen any repeated fields, i.e., the repetition level is 0.
> When we see 'en', field Language has repeated, so the repetition level is 2.
> Finally, when we encounter 'en-gb', Name has repeated most recently (Language occurred only once after Name), so the repetition level is 1.

笔者认为论文的解释有点模糊，按照以下步骤计算 repetition level 更为准确：

1. 深度优先遍历整棵树：
    1. 若字段是第一次出现，repetition level 记为 0 ；
    2. 若字段不是第一次出现：
        1. 找到上一次出现的同名字段；
        2. 找到最近公共祖先；
        3. 找到最近公共祖先的子节点；
        4. 计算最近公共祖先子节点在路径上是第几个 repeated （不包括 optional ）字段。

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/columnar-storage-dremel/r1-code-repetition-level-1.png)

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/columnar-storage-dremel/r1-code-repetition-level-2.png)

| value of Document.[Name].[Language].Code | repeated with | repeated at | common father of 'repeated at' | repetition level |
|                   :-:                    |      :-:      |     :-:     |              :-:               |       :-:        |
|                  en-us                   |               |             |                                |        0         |
|                    en                    |     en-us     |  Language   |              Name              |        2         |
|                  en-gb                   |      en       |    Name     |            Document            |        1         |

### Others

| value of Document.DocId | repeated with | repeated at | common father of 'repeated at' | repetition level |
|           :-:           |      :-:      |     :-:     |              :-:               |       :-:        |
|           10            |               |             |                                |        0         |

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/columnar-storage-dremel/r1-forward-repetition-level.png)

| value of Document.[Links].[Forward] | repeated with | repeated at | common father of 'repeated at' | repetition level |
|                 :-:                 |      :-:      |     :-:     |              :-:               |       :-:        |
|                 20                  |               |             |                                |        0         |
|                 40                  |      20       |   Forward   |             Links              |        1         |
|                 60                  |      40       |   Forward   |             Links              |        1         |

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/columnar-storage-dremel/r1-country-repetition-level.png)

| value of Document.[Name].[Language].Country | repeated with | repeated at | common father of 'repeated at' | repetition level |
|                     :-:                     |      :-:      |     :-:     |              :-:               |       :-:        |
|                     us                      |               |             |                                |        0         |
|                     gb                      |      us       |    Name     |            Document            |        1         |

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/columnar-storage-dremel/r1-url-repetition-level.png)

| value of Document.[Name].Url | repeated with | repeated at | common father of 'repeated at' | repetition level |
|             :-:              |      :-:      |     :-:     |              :-:               |       :-:        |
|           http://A           |               |             |                                |        0         |
|           http://B           |   http://A    |    Name     |            Document            |        1         |

## Definition Level

> Each value of a field with path p, **esp. every NULL**, has a definition level specifying how many fields in p that
> **could be undefined** (because they are optional or repeated) are **actually present** in the record.

在 Definition Level 小节，我们会使用 \[\] 和矩形表达 optional 字段**和** repeated 字段（注意与 Repetition Level 小节区分）。

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/columnar-storage-dremel/r1-url-definition-level.png)

| value of Document.[Name].[Url] | definition level |
|              :-:               |       :-:        |
|            http://A            |        2         |
|            http://B            |        2         |
|              null              |        1         |

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/columnar-storage-dremel/r1-country-definition-level.png)

| value of Document.\[Name\].\[Language\].\[Country\] | definition level |
|                         :-:                         |       :-:        |
|                         us                          |        3         |
|                        null                         |        2         |
|                        null                         |      **1**       |
|                         gb                          |        3         |

# 作图工具

# 参考资料

+ [Dremel: Interactive Analysis of Web-Scale Datasets](https://storage.googleapis.com/pub-tools-public-publication-data/pdf/36632.pdf)
+ [How to convert JSON data into a tree image?](https://stackoverflow.com/questions/40118113/how-to-convert-json-data-into-a-tree-image)
+ [Graphviz - Graph Visualization Software: The DOT Language](https://graphviz.org/doc/info/lang.html)
+ [Stack Overflow: Why doesn't fill color work with graphviz?](https://stackoverflow.com/questions/17252630/why-doesnt-fillcolor-work-with-graphviz)
