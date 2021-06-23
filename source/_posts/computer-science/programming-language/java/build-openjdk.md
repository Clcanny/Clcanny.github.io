---
title: Build OpenJDK
date: 2020-10-24 19:06:45
categories:
  - [Computer Science, Programming Language, Java]
---

# 背景

C++ 代码通过 JNI 调用 Java 代码，通过分析 coredump 发现 Java 代码占用大量虚存。

从 coredump 提取 Java heap dump 需要 JDK 版本完全一致，运行时的 JRE 版本和 jmap 版本甚至不能相差一个小版本，因而需要从头编译特定的 OpenJDK 。

# 编译 OpenJDK

编译 OpenJDK 有两点需要注意：

1. 在 2020 年，`debian:jessie` 自带的 `hg` 无法正常下载 OpenJDK 源代码并切分支；`debian:buster` 自带的 OpenJDK 无法作为 bootstrap JDK 来编译 jdk8u 。
2. 编译 OpenJDK 过程较慢，建议使用服务器（笔者使用的是 24 core 的抢占式实例）来编译；由于需要下载 OpenJDK 源代码，选用服务器时请考虑网络环境。

## 安装 Docker

```bash
curl -fsSL https://get.docker.com -o get-docker.sh
sudo sh get-docker.sh
sudo usermod -aG docker $USER
```

## 下载特定版本的 OpenJDK

`hg` 需要高于某个版本才能工作，这里选用 `debian:buster` 自带的 `hg` （特别提醒：`debian:jessie` 自带的 `hg` 是无法在 2020 年正常下载 OpenJDK 源代码并切分支的）。

```dockerfile
# download_openjdk.dockerfile
FROM debian:buster
LABEL maintainer="837940593@qq.com"

ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update
RUN apt-get install -y mercurial

# Download OpenJDK.
# https://hg.openjdk.java.net
RUN hg clone https://hg.openjdk.java.net/jdk8u/jdk8u jdk8u
WORKDIR /jdk8u
RUN bash get_source.sh
# Please find tags in https://hg.openjdk.java.net/jdk8u/jdk8u/tags.
# 25.65-b01 -> jdk8u65-b01

RUN hg up jdk8u65-b01 && hg id
RUN find . -type d -maxdepth 1 | xargs -n1 -Isubdir -- sh -c "cd subdir && hg up jdk8u65-b01 && hg id"
```

```bash
docker build -t download_openjdk:jdk8u65-b01 -f download_openjdk.dockerfile .
docker cp $(docker create --rm download_openjdk:jdk8u65-b01):/jdk8u .
```

## 编译 OpenJDK

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

ADD jdk8u /jdk8u
WORKDIR /jdk8u
# https://stackoverflow.com/questions/52377684/compile-jdk8-error-could-not-find-freetype
ENV DISABLE_HOTSPOT_OS_VERSION_CHECK ok
RUN bash configure --with-freetype-include=/usr/include/freetype2 --with-freetype-lib=/usr/lib/x86_64-linux-gnu

RUN make JOBS=24 all
RUN tar -czvf linux-x86_64-normal-server-release-jdk8u65-b01.tar.gz build
```

```bash
docker build -t build_openjdk:jdk8u65-b01 -f build_openjdk.dockerfile .
docker cp $(docker create --rm build_openjdk:jdk8u65-b01):/jdk8u/linux-x86_64-normal-server-release-jdk8u65-b01.tar.gz .
```

`linux-x86_64-normal-server-release-jdk8u65-b01.tar.gz` 在笔者的机器上是 1.3G ，文件太大不利于拷贝；也可以执行 `tar -czvf linux-x86_64-normal-server-release-jdk8u65-b01-tiny.tar.gz build/linux-x86_64-normal-server-release/jdk` 打包出一个仅为 223 MB 的包。

## 使用 jmap

```cpp
// generate_jni_core.cpp
#include <jni.h>

#include <cassert>
#include <cstdlib>
#include <cstring>

int main() {
    JNIEnv* env = nullptr;
    JavaVM* jvm = nullptr;

    JavaVMOption options[1];
    options[0].optionString = "-Djava.class.path=.";
    JavaVMInitArgs vm_args;
    std::memset(&vm_args, 0, sizeof(vm_args));
    vm_args.version = JNI_VERSION_1_2;
    vm_args.nOptions = 1;
    vm_args.options = options;

    assert(JNI_CreateJavaVM(&jvm, reinterpret_cast<void**>(&env), &vm_args) !=
           JNI_ERR);
    assert(env != nullptr);

    jclass cls = env->FindClass("SayHello");
    assert(cls != 0);
    jmethodID mid = env->GetStaticMethodID(cls, "sayHello", "()V");
    assert(mid != 0);
    env->CallStaticVoidMethod(cls, mid);
    std::abort();
}
```

```java
// SayHello.java
public class SayHello {
    public static void sayHello() {
        System.out.println("Hello!");
    }
}
```

用以下命令编译 C++ 代码和 Java 代码：

```bash
export JAVA_HOME=/linux-x86_64-normal-server-release/jdk
g++ -std=c++11 -O0 -ggdb generate_jni_core.cpp                                     \
    -I/linux-x86_64-normal-server-release/jdk/include                         \
    -I/linux-x86_64-normal-server-release/jdk/include/linux                   \
    -L/linux-x86_64-normal-server-release/jdk/lib/amd64/server                \
    -Wl,-rpath=/linux-x86_64-normal-server-release/jdk/lib/amd64/server -ljvm \
    -o generate_jni_core
build/linux-x86_64-normal-server-release/jdk/bin/javac SayHello.java
```

执行 generate_jni_core 以产生 coredump ：

```bash
ulimit -c unlimited
./generate_jni_core
```

用 jmap 从 coredump 中提取 Java heap dump ：

```bash
build/linux-x86_64-normal-server-release/jdk/bin/jmap \
    -dump:format=b,file=dump.hprof generate_jni_core core
```

# Reference

+ [Install Docker Engine on Debian](https://docs.docker.com/engine/install/debian/)
+ [Stack Overflow: Docker - how can I copy a file from an image to a host?](https://stackoverflow.com/questions/25292198/docker-how-can-i-copy-a-file-from-an-image-to-a-host)
+ [OpenJDK](https://openjdk.java.net/)
+ [Stack Overflow: Core dump taken with gcore, jmap conversion to hprof file format fails with Error message](https://stackoverflow.com/questions/9981080/core-dump-taken-with-gcore-jmap-conversion-to-hprof-file-format-fails-with-erro)

