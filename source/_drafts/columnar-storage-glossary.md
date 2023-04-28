---
layout: draft
title: columnar-storage-glossary
date: 2021-03-16 16:48:02
categories:
  - columnar storage
---

# 参考资料

[](https://storage.googleapis.com/pub-tools-public-publication-data/pdf/36632.pdf)
[](https://www.influxdata.com/blog/apache-arrow-parquet-flight-and-their-ecosystem-are-a-game-changer-for-olap/)
[](https://www.kdnuggets.com/2017/02/apache-arrow-parquet-columnar-data.html)
[](https://github.com/apache/arrow/tree/master/cpp/src/parquet)
[](https://github.com/apache/parquet-format)
[](https://arrow.apache.org/blog/2019/10/13/introducing-arrow-flight/)

[](https://docs.dremio.com/)
Columnar Cloud Cache
Data Reflections
Arrow Flight 只负责 Dremio 和 client 的数据传输

[](https://www.jianshu.com/p/65570efd0ca3)
SIGMOD / VLDB / ICDE / PODS

https://arrow.apache.org/docs/developers/cpp/building.html
https://arrow.apache.org/docs/developers/cpp/building.html
https://medium.com/@liam.su8/details-you-need-to-know-about-apache-parquet-d21ff720465e
https://github.com/apache/parquet-mr
https://blog.cloudera.com/speeding-up-select-queries-with-parquet-page-indexes/
https://github.com/apache/parquet-format/blob/master/PageIndex.md
https://issues.apache.org/jira/browse/PARQUET-922
    https://github.com/lekv/parquet-format/blob/babb3568ce1e96849e6d41c70afd823b90d3ba5e/PageIndex.md
dictionary_page_offset: https://github.com/apache/parquet-format/blob/master/Encodings.md#PLAIN
bloom_filter_offset: https://github.com/apache/parquet-format/blob/master/BloomFilter.md
DataPageHeader 里面有 Page 级别的统计信息

先用 parquet-mr 探索 parquet 文件格式
https://docs.cloudera.com/documentation/enterprise/latest/topics/cdh_ig_parquet.html#parquet_examples
https://arrow.apache.org/docs/python/parquet.html

import pyarrow.parquet as pq
import numpy as np
import pandas as pd
import pyarrow as pa
df = pd.DataFrame({'one': [-1, np.nan, 2.5],
                   'two': ['foo', 'bar', 'baz'],
                   'three': [True, False, True]},
                   index=list('abc'))
import pyarrow.parquet as pq
table = pa.Table.from_pandas(df)
pq.write_table(table, 'example.parquet')
