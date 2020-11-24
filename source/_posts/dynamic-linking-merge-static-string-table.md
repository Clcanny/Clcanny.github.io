---
layout: post
title: "Dynamic Linking: Merge Static String Table"
date: 2020-11-24 12:46:23
tags:
  - dynamic linking
---

```bash
od --skip-bytes=0x3650 --read-bytes=0x1fa --format=xC -c main
```

# 参考资料

+ [Stack Overflow: String table in ELF](https://stackoverflow.com/questions/11289843/string-table-in-elf)
