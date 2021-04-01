---
layout: post
title: "Columnar Storage: Get Started With Parquet"
date: 2021-03-31 18:44:24
tags:
  - columnar storage
---

# 环境

```dockerfile
FROM ubuntu:groovy
WORKDIR /root
RUN apt-get update
RUN apt-get install -y curl wget git

RUN apt-get install -y openjdk-15-jdk
ENV JAVA_HOME=/usr/lib/jvm/java-1.15.0-openjdk-amd64
ENV PATH="$PATH:$JAVA_HOME/bin"
RUN java --version

RUN apt-get install -y python3 python3-distutils python3-apt
RUN curl https://bootstrap.pypa.io/get-pip.py -o get-pip.py
RUN python3 get-pip.py

RUN wget https://mirror-hk.koddos.net/apache/spark/spark-3.1.1/spark-3.1.1-bin-hadoop2.7.tgz
RUN tar -xzvf spark-3.1.1-bin-hadoop2.7.tgz

RUN pip3 install parquet-cli

RUN apt-get install -y build-essential cmake make gcc g++
RUN git clone https://github.com/apache/arrow.git
WORKDIR /root/arrow
RUN git checkout 76d3c36006162766ec598442a0c0d2192f5e0d0b
RUN cd cpp && mkdir -p debug && cd debug
WORKDIR /root/arrow/cpp/debug
RUN cmake -DCMAKE_BUILD_TYPE=Debug -DARROW_PARQUET=ON -DARROW_WITH_SNAPPY=ON ..
RUN make -j8
RUN make install
ENV LD_LIBRARY_PATH="$LD_LIBRARY_PATH:/usr/local/lib"

WORKDIR /root
```

# 文件格式

# 读写 Parquet 文件

## 使用 PySpark 读写 Parquet 文件

```bash
# ./spark-3.1.1-bin-hadoop2.7/bin/pyspark --master local[4]
Spark context available as 'sc' (master = local[4], app id = local-1617201523606).
SparkSession available as 'spark'.
```

```python3
from pyspark.sql.types import *
schema = StructType([
    StructField("DocId", LongType(), nullable=False),
    StructField("Links", StructType([
        StructField("Backward", ArrayType(LongType()), nullable=True),
        StructField("Forward", ArrayType(LongType()), nullable=True)
    ]), nullable=True),
    StructField("Name", ArrayType(StructType([
        StructField("Language", ArrayType(StructType([
            StructField("Code", StringType(), nullable=False),
            StructField("Country", StringType(), nullable=True)
        ])), nullable=True),
        StructField("Url", StringType(), nullable=True)
    ])), nullable=True)
])
r1 = {
    "DocId": 10,
    "Links": {"Forward": [20, 40, 60]},
    "Name": [
        {
            "Language": [{"Code": "en-us", "Country": "us"}, {"Code": "en"}],
            "Url": "http://A"
        },
        {"Url": "http://B"},
        {"Language": [{"Code": "en-gb", "Country": "gb"}]}
    ]
}
r2 = {
    "DocId": 20,
    "Links": {"Backward": [10, 30, 80]},
    "Name": [{"Url": "http://C"}]
}
df = spark.createDataFrame([r1, r2], schema)
df.repartition(1).write.mode('overwrite').parquet("/root/dremel-records-pyspark.parquet")
```

```python3
df = spark.read.parquet("/root/dremel-records-pyspark.parquet")
df.createOrReplaceTempView("DremelRecords")
spark.sql("SELECT * FROM DremelRecords").show(truncate=False)
```

## 使用 C++ 读写 Parquet 文件

```cpp
// Refer arrow/cpp/examples/parquet/low-level-api/reader-writer.cc
// g++ -std=c++11 write_dremel_records.cpp -lparquet -larrow -o write_dremel_records.out
#include <arrow/io/file.h>
#include <parquet/api/writer.h>

#include <array>
#include <cassert>
#include <cstdint>
#include <exception>
#include <iostream>
#include <memory>

using parquet::schema::GroupNode;
using parquet::schema::NodeVector;
using parquet::schema::PrimitiveNode;

auto NONE = parquet::ConvertedType::NONE;
auto OPTIONAL = parquet::Repetition::OPTIONAL;
auto REPEATED = parquet::Repetition::REPEATED;
auto REQUIRED = parquet::Repetition::REQUIRED;
auto INT64 = parquet::Type::INT64;
auto BYTE_ARRAY = parquet::Type::BYTE_ARRAY;
auto UTF8 = parquet::ConvertedType::UTF8;

std::shared_ptr<GroupNode> SetUpSchema() {
    auto doc_id = PrimitiveNode::Make("DocId", REQUIRED, INT64, NONE);

    auto links = GroupNode::Make(
        "Links",
        OPTIONAL,
        NodeVector{PrimitiveNode::Make("Backward", REPEATED, INT64, NONE),
                   PrimitiveNode::Make("Forward", REPEATED, INT64, NONE)});

    auto code = PrimitiveNode::Make("Code", REQUIRED, BYTE_ARRAY, UTF8);
    auto country = PrimitiveNode::Make("Country", OPTIONAL, BYTE_ARRAY, UTF8);
    auto name = GroupNode::Make(
        "Name",
        REPEATED,
        NodeVector{
            GroupNode::Make("Language", REPEATED, NodeVector{code, country}),
            PrimitiveNode::Make("Url", OPTIONAL, BYTE_ARRAY, UTF8)});

    return std::static_pointer_cast<GroupNode>(
        GroupNode::Make("schema", REQUIRED, NodeVector{doc_id, links, name}));
}

void WriteRecords(parquet::RowGroupWriter* rg_writer) {
    parquet::Int64Writer* doc_id_writer =
        static_cast<parquet::Int64Writer*>(rg_writer->NextColumn());
    doc_id_writer->WriteBatch(2,
                              std::array<int16_t, 2>{0, 0}.data(),
                              std::array<int16_t, 2>{0, 0}.data(),
                              std::array<int64_t, 2>{10, 20}.data());

    parquet::Int64Writer* backward_writer =
        static_cast<parquet::Int64Writer*>(rg_writer->NextColumn());
    backward_writer->WriteBatch(3,
                                std::array<int16_t, 3>{1, 2, 2}.data(),
                                std::array<int16_t, 3>{0, 0, 1}.data(),
                                std::array<int64_t, 2>{10, 30}.data());

    parquet::Int64Writer* forward_writer =
        static_cast<parquet::Int64Writer*>(rg_writer->NextColumn());
    forward_writer->WriteBatch(4,
                               std::array<int16_t, 4>{2, 2, 2, 2}.data(),
                               std::array<int16_t, 4>{0, 1, 1, 0}.data(),
                               std::array<int64_t, 4>{20, 40, 60, 80}.data());

    parquet::ByteArrayWriter* code_writer =
        static_cast<parquet::ByteArrayWriter*>(rg_writer->NextColumn());
    code_writer->WriteBatch(
        5,
        std::array<int16_t, 5>{2, 2, 1, 2, 1}.data(),
        std::array<int16_t, 5>{0, 2, 1, 1, 0}.data(),
        std::array<parquet::ByteArray, 3>{parquet::ByteArray("en-us"),
                                          parquet::ByteArray("en"),
                                          parquet::ByteArray("en-gb")}
            .data());

    parquet::ByteArrayWriter* country_writer =
        static_cast<parquet::ByteArrayWriter*>(rg_writer->NextColumn());
    country_writer->WriteBatch(0, nullptr, nullptr, nullptr);
    country_writer->WriteBatch(
        5,
        std::array<int16_t, 5>{3, 2, 1, 3, 1}.data(),
        std::array<int16_t, 5>{0, 2, 1, 1, 0}.data(),
        std::array<parquet::ByteArray, 2>{parquet::ByteArray("us"),
                                          parquet::ByteArray("gb")}
            .data());

    parquet::ByteArrayWriter* url_writer =
        static_cast<parquet::ByteArrayWriter*>(rg_writer->NextColumn());
    url_writer->WriteBatch(
        4,
        std::array<int16_t, 4>{2, 2, 1, 2}.data(),
        std::array<int16_t, 4>{0, 1, 1, 0}.data(),
        std::array<parquet::ByteArray, 3>{parquet::ByteArray("http://A"),
                                          parquet::ByteArray("http://B"),
                                          parquet::ByteArray("http://C")}
            .data());
}

int main() {
    try {
        // Create a local file output stream instance.
        using FileClass = ::arrow::io::FileOutputStream;
        std::shared_ptr<FileClass> out_file;
        PARQUET_ASSIGN_OR_THROW(
            out_file, FileClass::Open("/root/dremel-records-cpp.parquet"));

        // Setup the parquet schema.
        auto schema = SetUpSchema();

        // Add writer properties.
        parquet::WriterProperties::Builder builder;
        builder.compression(parquet::Compression::SNAPPY);
        std::shared_ptr<parquet::WriterProperties> props = builder.build();

        // Create a ParquetFileWriter instance.
        std::shared_ptr<parquet::ParquetFileWriter> file_writer =
            parquet::ParquetFileWriter::Open(out_file, schema, props);

        // Append a RowGroup with a specific number of rows.
        parquet::RowGroupWriter* rg_writer = file_writer->AppendRowGroup();
        WriteRecords(rg_writer);

        // Close the ParquetFileWriter.
        file_writer->Close();

        // Write the bytes to file.
        assert(out_file->Close().ok());
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Parquet write error: " << e.what() << std::endl;
        return -1;
    }
}
```

## 使用 [chhantyal/parquet-cli](https://github.com/chhantyal/parquet-cli) 读 Parquet 文件

```bash
# parq /root/dremel-records.parquet/part-00000-14a09068-9f6d-4515-a176-dccf6836ee11-c000.snappy.parquet
# parq /root/dremel-records.parquet/part-00000-14a09068-9f6d-4515-a176-dccf6836ee11-c000.snappy.parquet --schema
```

# 参考资料

+ [Spark Programming Guide](https://spark.apache.org/docs/2.1.1/programming-guide.html#using-the-shell)
+ [Spark By Examples: PySpark Read and Write Parquet File](https://sparkbyexamples.com/pyspark/pyspark-read-and-write-parquet-file/)
+ [Spark By Examples: PySpark StructType & StructField Explained with Examples](https://sparkbyexamples.com/pyspark/pyspark-structtype-and-structfield/)
+ [Apache Spark User List: dremel paper example schema](http://apache-spark-user-list.1001560.n3.nabble.com/dremel-paper-example-schema-td33817.html)
+ [Medium: Install Apache Spark (pyspark) — Standalone mode](https://medium.com/@sivachaitanya/install-apache-spark-pyspark-standalone-mode-70d3c2dd8924)
+ [Techoral: OpenJDK 15 Download and Installation on Ubuntu](https://techoral.com/blog/java/install-openjdk-15-ubuntu.html)
+ [Apache Arrow: Building Arrow C++](https://arrow.apache.org/docs/developers/cpp/building.html)
