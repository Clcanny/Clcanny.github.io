---
layout: post
title: Perf JNI Program
date: 2021-11-26 19:57:49
categories:
  - [Computer Science, Performance Analysis]
---

# 如何下载 OpenJDK 的源代码？

OpenJDK 的源代码可以从以下网址找：

+ [GitHub: openjdk/jdk](https://github.com/openjdk/jdk)
+ [OpenJDK projects](https://hg.openjdk.java.net/)

笔者目前工作中用到的 JDK 是 jdk1.8.0\_131 ，最接近的版本是：

+ [GitHub: openjdk/jdk jdk8-b120](https://github.com/openjdk/jdk/tree/jdk8-b120)
+ [OpenJDK projects: changeset 940:2a8f4c022aa0, Added tag jdk8-b131 for changeset 0c38dfecab2a](https://hg.openjdk.java.net/jdk8/jdk8/rev/2a8f4c022aa0)

`hg.openjdk.java.net` 的稳定性不好，容易报错 http code 500 ，所以我们按照 commit 信息 Added tag jdk8-b131 for changeset 0c38dfecab2a 到 GitHub 上找到对应的 commit id `8bc9bd48f9d7ab758aede3be36318fe012c78863` ，然后用 git 下载代码。

`hg` 需要高于某个版本才能工作，这里选用 `debian:buster` 自带的 `hg` （特别提醒：`debian:jessie` 自带的 `hg` 是无法在 2021 年正常下载 OpenJDK 源代码并切分支的）。

```dockerfile
# download_openjdk.dockerfile
FROM debian:buster
LABEL maintainer="837940593@qq.com"

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -y mercurial

# Download OpenJDK.
RUN hg clone https://hg.openjdk.java.net/jdk8u/jdk8u jdk8u
WORKDIR /jdk8u
RUN bash get_source.sh

RUN hg up jdk8u131-b01 && hg id
RUN find . -type d -maxdepth 1 | xargs -n1 -Isubdir -- sh -c "cd subdir && hg up jdk8u131-b01 && hg id"
```

```bash
# docker build -t download_openjdk:jdk8u131-b01 -f download_openjdk.dockerfile .
# docker cp $(docker create --rm download_openjdk:jdk8u131-b01):/jdk8u .
```

# 如何编译 OpenJDK ？

perf 需要符号表才能正确插入 uprobe ，所以编译 OpenJDK 时需要顺带编译符号表。有关符号的编译选项可以参考：

+ [腾讯云：Centos 编译 JDK8 源码](https://cloud.tencent.com/developer/article/1701909)
+ [OpenJDK building.md: Configure Arguments for Tailoring the Build](https://github.com/openjdk/jdk/blob/master/doc/building.md#configure-arguments-for-tailoring-the-build)
+ [OpenJDK building.md: Native Debug Symbols](https://github.com/openjdk/jdk/blob/master/doc/building.md#native-debug-symbols)

根据 [Stack Overflow: Scrambled arguments when building OpenJDK](https://stackoverflow.com/questions/21246042/scrambled-arguments-when-building-openjdk) 和 [JDK BUG SYSTEM: adjust-mflags.sh failed build with GNU Make 4.0 with -I\<path contains j\>](https://bugs.openjdk.java.net/browse/JDK-8028407) 的说法，`make` 不能使用 4.0 及以上版本，否则会报错：

```bash
/usr/bin/make: invalid option -- '8'
/usr/bin/make: invalid option -- 'u'
/usr/bin/make: invalid option -- '/'
/usr/bin/make: invalid option -- 'a'
/usr/bin/make: invalid option -- '/'
/usr/bin/make: invalid option -- 'c'
```

```dockerfile
# build_openjdk.dockerfile
FROM debian:jessie
LABEL maintainer="837940593@qq.com"

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update

RUN apt-get install -y cpio file build-essential make zip unzip
RUN apt-get install -y libX11-dev libxext-dev libxrender-dev libxtst-dev libxt-dev
RUN apt-get install -y libcups2-dev
RUN apt-get install -y libfreetype6-dev
RUN apt-get install -y libasound2-dev
RUN apt-get install -y libfontconfig1-dev
# Install boot jdk.
RUN apt-get install -y openjdk-7-jdk

# Downgrade make to 3.82.
WORKDIR /tmp
RUN apt-get install -y wget
RUN wget https://ftp.gnu.org/gnu/make/make-3.82.tar.gz --no-check-certificate
RUN tar -xzvf make-3.82.tar.gz
WORKDIR /tmp/make-3.82
RUN ./configure --prefix=/usr
RUN make && make install
RUN make --version

ADD jdk8u /jdk8u
WORKDIR /jdk8u
# https://stackoverflow.com/questions/52377684/compile-jdk8-error-could-not-find-freetype
ENV DISABLE_HOTSPOT_OS_VERSION_CHECK ok
RUN bash configure --with-freetype-include=/usr/include/freetype2 \
                   --with-freetype-lib=/usr/lib/x86_64-linux-gnu  \
                   --with-debug-level=release                     \
                   --enable-debug-symbols
RUN make JOBS=8 all
RUN tar -czvf linux-x86_64-normal-server-release-jdk8-b131.tar.gz build
```

```bash
# docker build -t build_openjdk:jdk8-b131 -f build_openjdk.dockerfile .
```
