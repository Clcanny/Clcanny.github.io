---
layout: post
title: bug-when-use-ssh-in-python
date: 2021-12-24 00:04:08
id: b22afd5d5c153cd6d0ea083e8ad8dedd
tags:
---

According to [paramiko/paramiko: hanging on stdout.readlines\(\), Pierce Lopez's comment](https://github.com/paramiko/paramiko/issues/109#issuecomment-464505837):

> The general issue here is that you must also read stderr. If you just read stdout, it's possible that the process wrote "too much" to stderr, so it could not all be buffered, and the process is blocked writing more to stderr, waiting for what was already written to be read.

```python
#!/usr/bin/python2.7
```

