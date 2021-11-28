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

+ perf 需要符号表才能正确插入 uprobe ，所以编译 OpenJDK 时需要顺带编译符号表。有关符号的编译选项可以参考：
  + [腾讯云：Centos 编译 JDK8 源码](https://cloud.tencent.com/developer/article/1701909)
  + [OpenJDK building.md: Configure Arguments for Tailoring the Build](https://github.com/openjdk/jdk/blob/master/doc/building.md#configure-arguments-for-tailoring-the-build)
  + [OpenJDK building.md: Native Debug Symbols](https://github.com/openjdk/jdk/blob/master/doc/building.md#native-debug-symbols)
+ 根据 [Stack Overflow: Scrambled arguments when building OpenJDK](https://stackoverflow.com/questions/21246042/scrambled-arguments-when-building-openjdk) 和 [JDK BUG SYSTEM: adjust-mflags.sh failed build with GNU Make 4.0 with -I\<path contains j\>](https://bugs.openjdk.java.net/browse/JDK-8028407) 的说法，`make` 不能使用 4.0 及以上版本，否则会报错：

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
ENV JAVA_HOME /jdk8u/build/linux-x86_64-normal-server-release/jdk
RUN cmake .
RUN make
RUN tar -czvf perf-map-agent-jdk8u131-b11.tar.gz \
              bin                                \
              out/attach-main.jar                \
              out/libperfmap.so
```

```bash
# docker build -t build_perf_map_agent:jdk8u131-b11 -f build_perf_map_agent.dockerfile .
# docker cp $(docker create --rm build_perf_map_agent:jdk8u131-b11):/perf-map-agent/perf-map-agent-jdk8u131-b11.tar.gz .
```

# 一个简单的例子

```java
// HelloWorld.java
public class HelloWorld {
  public void sleep() {
    sleepInSynchronizedArea();
  }

  private synchronized void sleepInSynchronizedArea() {
    try {
      Thread.sleep(1000);
    } catch (InterruptedException e) {
    }
  }

  public void sayHelloWorld() {
    sayHelloWorldInSynchronizedArea();
  }

  private synchronized void sayHelloWorldInSynchronizedArea() {
    System.out.println("Hello, world!");
  }
}
```

```cpp
// main.cpp
#include <jni.h>
#include <pthread.h>

#include <cassert>
#include <chrono>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <thread>

void print_time() {
  using std::chrono::duration_cast;
  using std::chrono::milliseconds;
  using std::chrono::system_clock;
  std::cout << duration_cast<milliseconds>(
                 system_clock::now().time_since_epoch())
                 .count()
            << std::endl;
}

void say_hello(JNIEnv* env, jobject obj, jmethodID mid) {
  env->CallVoidMethod(obj, mid);
}

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

  jclass cls = env->FindClass("HelloWorld");
  assert(cls != 0);
  jobject obj = env->AllocObject(cls);
  jmethodID sleep_mid = env->GetMethodID(cls, "sleep", "()V");
  assert(sleep_mid != 0);
  jmethodID say_hello_mid = env->GetMethodID(cls, "sayHelloWorld", "()V");
  assert(say_hello_mid != 0);

  std::thread sleep_thread([jvm, obj, sleep_mid]() {
    pthread_setname_np(pthread_self(), "sleep-thread");
    JNIEnv* env = nullptr;
    jvm->AttachCurrentThread(reinterpret_cast<void**>(&env), nullptr);
    assert(env != nullptr);
    while (true) {
      env->CallVoidMethod(obj, sleep_mid);
      std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
  });
  std::thread say_hello_thread([jvm, obj, say_hello_mid]() {
    pthread_setname_np(pthread_self(), "say-hello-thread");
    JNIEnv* env = nullptr;
    jvm->AttachCurrentThread(reinterpret_cast<void**>(&env), nullptr);
    assert(env != nullptr);
    while (true) {
      print_time();
      say_hello(env, obj, say_hello_mid);
      print_time();
      std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
  });
  sleep_thread.join();
  say_hello_thread.join();
}
```

```bash
./build/linux-x86_64-normal-server-release/jdk/bin/javac HelloWorld.java
g++ -std=c++11 -O0 -ggdb main.cpp                                            \
  -I./build/linux-x86_64-normal-server-release/jdk/include                   \
  -I./build/linux-x86_64-normal-server-release/jdk/include/linux             \
  -L./build/linux-x86_64-normal-server-release/jdk/lib/amd64/server          \
  -Wl,-rpath=./build/linux-x86_64-normal-server-release/jdk/lib/amd64/server \
  -ljvm -lpthread -lunwind                                                   \
  -o main
```

# 分析

## 插入 uprobe

perf probe 的命令格式可以参考 [perf-probe(1) — Linux manual page](https://man7.org/linux/man-pages/man1/perf-probe.1.html) ，值得注意的是：

> PROBE SYNTAX
> Probe points are defined by following syntax.
> 1) Define event based on function name
>    [[GROUP:]EVENT=]FUNC[@SRC][:RLN|+OFFS|%return|;PTN] [ARG ...]

以函数 `say_hello` 的 return probe 为例：

```bash
        exit_say_hello=_Z9say_helloP7JNIEnv_P8_jobjectP10_jmethodID%return
[GROUP:]EVENT         =FUNC                                        %return
```

```bash
# whoami
root
# readelf --wide --symbols main | grep say_hello
113: 0000000000001850 7 FUNC GLOBAL DEFAULT 14 _Z9say_helloP7JNIEnv_P8_jobjectP10_jmethodID
# perf probe -x main --add entry_say_hello=_Z9say_helloP7JNIEnv_P8_jobjectP10_jmethodID
# perf probe -x main --add exit_say_hello=_Z9say_helloP7JNIEnv_P8_jobjectP10_jmethodID%return
# cat /sys/kernel/debug/tracing/uprobe_events
p:probe_main/enter_say_hello /home/demons/build/main:0x000000000000122d
r:probe_main/exit_say_hello /home/demons/build/main:0x000000000000122d
# perf list | grep probe_main
probe_main:entry_say_hello                         [Tracepoint event]
probe_main:exit_say_hello                          [Tracepoint event]
```

## 跟踪 `say_hello` 函数耗时

```bash
# perf record
Usage: perf record [<options>] [<command>]
   or: perf record [<options>] -- <command> [<options>]
   -R, --raw-samples     collect raw sample records from all opened counters
```

```bash
# perf record -e probe_main:entry_say_hello -e probe_main:exit_say_hello -R -p 3429
[ perf record: Woken up 1 times to write data ]
[ perf record: Captured and wrote 0.090 MB perf.data (15 samples) ]
# perf script | head -n 4
main  3449 [004] 22430.470425: probe_main:entry_say_hello: (556a3249122d)
main  3449 [004] 22431.470482:  probe_main:exit_say_hello: (556a3249122d <- 556a3249137f)
main  3449 [004] 22431.570604: probe_main:entry_say_hello: (556a3249122d)
main  3449 [004] 22432.570643:  probe_main:exit_say_hello: (556a3249122d <- 556a3249137f)
```

根据 [Stack Overflow: What is meaning of timestamp in perf?](https://stackoverflow.com/questions/61425982/what-is-meaning-of-timestamp-in-perf) 的说法：

> Timestamps "X.Y" in perf output are X seconds and Y microseconds. In `perf script` output it probably X seconds since linux boot. Similar time format is used in `dmesg` output.

我们发现每次执行 `say_hello` 函数都需要 1s+ 。那为什么一个这么简单的函数会耗时这么久？

## 分析 `say_hello` 函数是 CPU 密集型还是 IO 密集型

当前线程出让 CPU 时会触发 `sched:sched_switch` 事件，当前线程获得 CPU 时会触发 `sched:sched_wakeup` 事件，我们可以利用这两个事件判断线程究竟是在等锁（ IO ）还是在执行耗 CPU 的代码。

根据 [Basic Usage (with examples) for each of the Yocto Tracing Tools: Filtering](https://docs.yoctoproject.org/profile-manual/usage.html#filtering) 的介绍，perf event 支持过滤器，过滤掉我们不关心的事件。`sched:sched_switch` 支持 `--filter '(prev_pid >= xxx && prev_pid <= xxx) || (next_pid >= xxx && next_pid <= xxx)'` ，`sched:sched_wakeup` 支持 `--filter '(pid <= xxx && pid >= xxx)'` ，在目标进程拥有多个线程的情况下，这两个 filter 能过滤掉大量无关事件。需要说明的是 filter 中的 `pid` 是 thread id 。

```bash
# ps aux | grep main | awk '{print $2}'
4340
# ps -eT | grep 4340
4340  4359 pts/0    00:00:00 sleep-thread
4340  4360 pts/0    00:00:01 sh-thread
```

```bash
perf record                                                             \
  -e probe_main:entry_say_hello -e probe_main:exit_say_hello            \
  -e sched:sched_switch --filter 'prev_pid == 5292 || next_pid == 5292' \
  -e sched:sched_wakeup --filter 'pid == 5292'                          \
  -R -p 5272
```

```text
   sh-thread  5292 [005] 39159.217868: probe_main:entry_say_hello: (55e0d310d2ed)
   sh-thread  5292 [005] 39159.217919: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

     swapper     0 [005] 39159.218968: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39159.218977: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

     swapper     0 [005] 39159.227033: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39159.227041: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

     swapper     0 [005] 39159.291101: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39159.291113: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

     swapper     0 [005] 39159.803180: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39159.803206: sched:sched_switch: sh-thread:5292 [120] S ==> swapper/5:0 [120]

sleep-thread  5291 [003] 39160.217827: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
sleep-thread  5291 [003] 39160.217831: sched:sched_wakeup: sh-thread:5292 [120] success=1 CPU:005
   sh-thread  5292 [005] 39160.217958: probe_main:exit_say_hello: (55e0d310d2ed <- 55e0d310d467)
```

从 perf 的结果看，线程 `sh-thread` 每次获得 CPU 时间片（发生 `sched:sched_wakeup` 事件）之后，都会在 10 微秒后切走（发生 `sched:sched_switch` 事件）。下次要在几毫秒 ~ 几百毫秒之后才能获得 CPU 时间片。因此，这是一个 IO 密集型函数。
