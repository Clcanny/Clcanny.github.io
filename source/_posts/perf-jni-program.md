---
layout: post
title: Perf JNI Program
date: 2021-11-26 19:57:49
categories:
  - [Computer Science, Performance Analysis]
---

# 如何确认 OpenJDK 的版本号？

用 [arthas dashboard](https://arthas.aliyun.com/doc/en/dashboard.html) 命令可以查看运行进程的 Java 位置：

```bash
# java -jar arthas-boot.jar 156
# dashboard
java.home /usr/lib/jvm/java-8-oracle/jre
```

再用 `java -version` 命令来查看版本号：
```bash
# /usr/lib/jvm/java-8-oracle/jre/bin/java -version
java version "1.8.0_40"
Java(TM) SE Runtime Environment (build 1.8.0_40-b25)
Java HotSpot(TM) 64-Bit Server VM (build 25.40-b25, mixed mode)
```

笔者工作中用到的 OpenJDK build 是 1.8.0\_131-b11 ，下文都会使用这个版本的 OpenJDK 。

# 如何下载 OpenJDK 的源代码？

OpenJDK 的源代码可以从以下网址找：

+ [GitHub: openjdk/jdk](https://github.com/openjdk/jdk)
+ [GitHub: openjdk/jdk8u](https://github.com/openjdk/jdk8u)
+ [OpenJDK projects](https://hg.openjdk.java.net/)
+ [OpenJDK projects: jdk8u/jdk8u/tags](https://hg.openjdk.java.net/jdk8u/jdk8u/tags)

笔者目前工作中用到的 JDK 是 jdk1.8.0\_131-b11 ，最接近的版本是：

+ [GitHub: openjdk/jdk8u jdk8u131-b11](https://github.com/openjdk/jdk8u/tree/jdk8u131-b11)
+ [OpenJDK projects: changeset 1915:94b119876028, Added tag jdk8u131-b10 for changeset 725620ca52fb](https://hg.openjdk.java.net/jdk8u/jdk8u/rev/94b119876028)

```bash
git clone https://github.com/openjdk/jdk8u.git
git checkout jdk8u131-b11
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

RUN apt-get install -y git
RUN git clone https://github.com/openjdk/jdk8u.git /jdk8u
WORKDIR /jdk8u
RUN git checkout -b jdk8u131-b11
# https://stackoverflow.com/questions/52377684/compile-jdk8-error-could-not-find-freetype
ENV DISABLE_HOTSPOT_OS_VERSION_CHECK ok
RUN bash configure --with-freetype-include=/usr/include/freetype2 \
                   --with-freetype-lib=/usr/lib/x86_64-linux-gnu  \
                   --with-debug-level=release                     \
                   --enable-debug-symbols
RUN make JOBS=8 all
RUN tar -czvf linux-x86_64-normal-server-release-jdk8u131-b11.tar.gz build
```

```bash
# docker build -t build_openjdk:jdk8u131-b11 -f build_openjdk.dockerfile .
# docker cp $(docker create --rm build_openjdk:jdk8u131-b11):/jdk8u/linux-x86_64-normal-server-release-jdk8u131-b11.tar.gz .
```

# 用 perf-map-agent 提供 Java 调用栈

JIT 会动态地将热点代码编译成 native code ，这会导致 perf 没有这部分代码的符号表，从而不认识相关函数。[perf-map-agent](https://github.com/jvm-profiling-tools/perf-map-agent) 就是为了解决这个问题而诞生的。

> Linux `perf` tools will expect symbols for code executed from unknown memory regions at `/tmp/perf-<pid>.map`. This allows runtimes that generate code on the fly to supply dynamic symbol mappings to be used with the `perf` suite of tools.
> perf-map-agent is an agent that will generate such a mapping file for Java applications. It consists of a Java agent written C and a small Java bootstrap application which attaches the agent to a running Java process.

```dockerfile
# build_perf_map_agent.dockerfile
FROM build_openjdk:jdk8u131-b11
RUN apt-get install -y cmake

RUN git clone https://github.com/jvm-profiling-tools/perf-map-agent.git /perf-map-agent
WORKDIR /perf-map-agent
ENV JAVA_HOME /jdk8u/build
RUN cmake ..
RUN make
RUN tar -czvf perf-map-agent-jdk8u131-b11.tar.gz \
              bin                                \
              out/attach-main.jar                \
              out/libperfmap.so
```
