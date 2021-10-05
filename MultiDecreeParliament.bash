java -Xms120g -XX:+UseParallelGC -XX:MaxDirectMemorySize=120g -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -cp /usr/local/lib/tla2tools.jar tlc2.TLC MultiDecreeParliament -workers auto -checkpoint 0

```bash
export JAVA_OPTS="-Xms80g -XX:+UseParallelGC"
tlc MultiDecreeParliament -workers auto -fpmem 0.9
# TLC2 Version 2.18 of Day Month 20?? (rev: 5b3286b)
# Running breadth-first search Model-Checking with fp 67 and seed -3575407683455352067 with 40 workers on 40 cores with 78507MB heap and 64MB offheap memory [pid: 2489] (Linux 3.10.0-1160.90.1.el7.x86_64 amd64, Red Hat, Inc. 11.0.19 x86_64, MSBDiskFPSet, DiskStateQueue).
# ...
# Starting... (2023-07-23 19:10:15)
# Implied-temporal checking--satisfiability problem has 1 branches.
# Checking temporal properties for the complete state space with 65659825 total distinct states at (2023-07-23 22:04:41)
# Finished checking temporal properties in 29min 58s at 2023-07-23 22:34:40
# Model checking completed. No error has been found.
#   Estimates of the probability that TLC did not check all reachable states
#   because two distinct states had the same fingerprint:
#   calculated (optimistic):  val = .0025
#   based on the actual fingerprints:  val = 6.8E-5
# 763561969 states generated, 65659825 distinct states found, 0 states left on queue.
# The depth of the complete state graph search is 33.
# The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 13 and the 95th percentile is 3).
# Finished in 03h 24min at (2023-07-23 22:34:47)
```
