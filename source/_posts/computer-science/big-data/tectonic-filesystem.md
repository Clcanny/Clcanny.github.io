---
title: Facebook's Tectonic Filesystem: Efficiency from Exascale
date: 2021-09-04 22:00:00
categories:
  - [Computer Science, Big Data]
---
<!--more-->

# 为什么把不同的存储系统整合成 Tectonic ？

Facebook 用 Haystack 和 f4 支撑对象存储，用 HDFS 支撑数据仓库。把这 3 套系统整合成 Tectonic 的动力来源于两方面：

+ 运维成本高，运维人员要熟悉 3 套存储系统；
+ [IOPS](https://en.wikipedia.org/wiki/IOPS) 和磁盘容量利用率低，以 Haystack 和 f4 为例：
  + Haystack 存储读写频繁的热数据，导致上层业务不能写满 Haystack 的磁盘，否则有限的 IOPS 无法服务如此多的读写请求；
  + f4 存储读写不频繁的冷数据，导致上层业务无法充分利用 f4 磁盘的 IOPS ；
  + 根据 [HDD UserBenchmark](https://hdd.userbenchmark.com/) 的数据，磁盘容量变大的同时，IOPS 并没有提升，导致 IOPS per byte 近几年在下降。这会进一步降低 IOPS 和磁盘容量的利用率。

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/computer-science/big-data/tectonic-filesystem/hddd-userbenchmark.png)

提升资源利用率有两种思路：

+ 分离不同类型的资源，如存储计算分离、IOPS-Storage 分离；
+ [混部](https://zhuanlan.zhihu.com/p/33780875)（ co-loaction ）：将不同类型的任务调度到相同的物理资源上。
  + Tectonic 的思路就是混部；
  + 混部要想达到 100% 资源利用率，对任务配比是有要求的。

$x_a$
