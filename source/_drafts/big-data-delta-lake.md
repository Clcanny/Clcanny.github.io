---
layout: draft
title: "Delta Lake"
date: 2021-05-23 00:21:03
tags:
  - big data
---

# 概述

大数据掀起数据湖风潮，阿里、腾讯等巨头都发布了自己的数据湖产品。本文会以 Delta Lake 为例，探讨：

1. 什么是 Lakehouse ？
2. Lakehouse 架构。

# 什么是 Lakehouse ？

Lakehouse 是融合数据仓库和数据湖优势的大数据系统：

开放性。对数据的掌控能力。

1. 融合数据仓库优势：
  1. 取得 SQL 优势。

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/big-data-delta-lake/what-is-lakehouse.png)

大纲笔记可访问[幕布](https://share.mubu.com/doc/7RYdZfE818f)。

# 数据湖架构

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/big-data-delta-lake/delta-lake-implementation.png)

大纲笔记可访问[幕布](https://share.mubu.com/doc/6qkt1FAt8of)。

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/big-data-delta-lake/objects-stored-in-a-sample-delta-table.png)

# 参考资料

+ [Build Lakehouses with Delta Lake](https://delta.io/)
+ [Lakehouse: A New Generation of Open Platforms that Unify Data Warehousing and Advanced Analytics](http://cidrdb.org/cidr2021/papers/cidr2021_paper17.pdf)
+ [Delta Lake: High-Performance ACID Table Storage over Cloud Object Stores](https://databricks.com/wp-content/uploads/2020/08/p975-armbrust.pdf)
+ [Cloudera Documentation: Introducing the S3A Committers](https://docs.cloudera.com/HDPDocuments/HDP3/HDP-3.0.1/bk_cloud-data-access/content/ch03s08s01.html)
+ [飞总聊 IT ：DataBricks 新项目 Delta Lake 的深度分析和解读](https://mp.weixin.qq.com/s/j7ja_pzHsT519u-maP4T-A)
+ [知乎：深度对比 delta 、iceberg 和 hudi 三大开源数据湖方案](https://zhuanlan.zhihu.com/p/110748218)
