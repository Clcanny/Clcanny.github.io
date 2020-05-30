---
title: Spark useful tips
date: 2020-05-3 12:50:00
tags:
  - Spark
---
<!--more-->

# 常用的 Spark 套路

## 应用内重试

```scala
def runQuery() = spark.readStream.writeStream.start()
while (true) {
  try {
    val query = runQuery()
    query.awaitTermination()
  } catch {
    case e: Throwable =>
    if (!meetConditionsForRetry()) {
      logError(s"Query exit: $e")
      throw e
    } else {
      logWarnning(s"Query stop: $e")
      // Sleep.
    }
  }
}
```

## Spark 重试

根据 [Running Spark on YARN](https://spark.apache.org/docs/latest/running-on-yarn.html) 文档，设置重试需要两个参数：

spark.yarn.am.attemptFailuresValidityInterval: Defines the validity interval for AM failure tracking. If the AM has been running for at least the defined interval, the AM failure count will be reset. This feature is not enabled if not configured.

spark.yarn.maxAppAttempts: The maximum number of attempts that will be made to submit the application. It should be no larger than the global number of max attempts in the YARN configuration.

两个配置联手可以达到：Spark App 最多在 spark.yarn.am.attemptFailuresValidityInterval 时间内连续重启 spark.yarn.maxAppAttempts 次而不失败

## Broadcast

Spark 支持 join 静态表，但很多时候我们希望这张静态表每隔一段时间能更新一次，Boradcast 可以实现这个需求

```scala
object Main extends Logging {
  // 1.
  @transient var broadcastValue: Option[String] = None
  val threadPool = new ScheduledThreadPool(1)
  val updateBroadcastValue = new Runnable {
    override def run(): Unit = {
      // Update boardcastValue here.
    }
  }
  threadPool.scheduleAtFixedRate(updateBroadcastValue, 0, 1, TimeUnit.MINUTES)

  // 2.
  var broadcast = spark.sparkContext.broadcast("")
  val broadcastListener = new StreamingQueryListener {
    override def onQueryStarted(event: QueryStartedEvent): Unit = {}

    override def onQueryProgress(event: QueryProgressEvent): Unit = {
      broadcast = broadcastValue.flatMap(v => {
        if (!spark.sparkContext.isStopped) {
          // Unpersist broadcast blocking.
          broadcast.unpersist(true)
          broadcast = spark.sparkContext.broadcast(v)
          logInfo(s"Update broadcast succeed: $v")
        }
      })
    }
  }

  // 3.
  val query = spark.readStream.mapPartitions(itPartition => {
    val value = broadcast.value
    // Do other things.
  })
}
```

1. broadcastValue 是定时更新的变量，将会通过 broadcast 从 Driver 发送到 Executor
2. broadcast 是将 broadcastValue 从 Driver 发送到 Executor 的变量，发起一次传输的条件是：即将开始一个 Spark Job 且 broadcastValue 尚未被更新过
3. mapPartitions 可以保证一个 partition 只读取一次 broadcast ，减少读取次数

## 合理设置分区数

spark.sql.shuffle.partitions 的默认值是 200 ，且 Spark 在同一个 Executor 上的 Task 不会并发执行

一个 partition 会用一个 Task 去跑，假设只有一个 Executor ，那么你将会看到 200 个 Task 顺序执行

每个 Task 执行时都会访问 HDFS 去获取自己的状态（日志表现为 HDFSStateStore ），这些 IO 操作加起来的时间会很可观，大大拖慢处理速度

建议设置分区数的时候考虑两点：

1. 数据量大小
2. 每个 Executor 尽量只有一个 Task （减少单个 Executor 访问 HDFS 的次数）

重新设置分区数后，要删除原有的 checkpoint 才能生效（猜测是 Spark 不具备扩张或合并 State ）的能力

## 重定向日志

常规的使用 log4j.properties 的方法有两个缺点：

1. 不太好配置
2. 如果重定向日志到服务器，accessId / accessKey 会被打包到 jar 中

这里介绍如何用代码配置 log4j （Spark 也支持 log4j2 ）

```scala
import org.apache.log4j.AppenderSkeleton

class MyAppender extends AppenderSkeleton {
  override def activateOptions(): Unit = {}

  override def append(event: LoggingEvent): Unit = {}
}
```

具体实现可以参考[阿里云 LoghubAppender 的实现](https://github.com/aliyun/aliyun-log-log4j-appender/blob/master/src/main/java/com/aliyun/openservices/log/log4j/LoghubAppender.java)

accessId / accessKey 可以从 `SparkEnv.get.conf` 里面读出来，这样就可以避免 jar 中包含 accessId / accessKey

设置 Executor log4j properties 的代码如下，参考 [Set executor log level](https://kb.databricks.com/clusters/set-executor-log-level.html) ：

```scala
spark.sparkContext.parallelize(Seq("")).foreachPartition(_ => {
  val rootLogger = Logger.getRootLogger
  val myAppender = new MyAppender()
  myAppender.activateOptions()
  // rootLogger.removeAllAppenders()
  rootLogger.addAppender(myAppender)
})
```
