---
layout: post
title: Iptables And K8S
date: 2021-07-04 18:27:04
categories:
  - [Computer Science, Tools, Network]
---

# Iptables

[CentOS: Iptables](https://wiki.centos.org/HowTos/Network/IPTables) 说 Netfilter 是工作在内核的模块，Iptables 是工作在用户空间、负责定义规则的命令行工具：

> Iptables is the userspace module, the bit that you, the user, interact with at the command line to enter firewall rules into predefined tables. Netfilter is a kernel module, built into the kernel, that actually does the filtering.

## 基本概念

### [Tables](https://ipset.netfilter.org/iptables.man.html)

> There are currently five independent tables (which tables are present at any time depends on the kernel configuration options and which modules are present).
>
> + filter
> + nat: This table is consulted when a packet that creates a new connection is encountered.
> + mangle: This table is used for specialized packet alteration. Until kernel 2.4.17 it had two built-in chains: **PREROUTING** (for altering incoming packets before routing) and **OUTPUT** (for altering locally-generated packets before routing). Since kernel **2.4.18**, three other built-in chains are also supported: **INPUT** (for packets coming into the box itself), **FORWARD** (for altering packets being routed through the box), and **POSTROUTING** (for altering packets as they are about to go out).
> + raw: This table is used mainly for configuring exemptions from connection tracking in combination with the NOTRACK target.
> + security

### [Chains](https://wiki.archlinux.org/title/Iptables#Chains)

> Tables consist of chains, which are lists of rules which are followed in order.

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/iptables-and-k8s/tables_traverse.jpg)

### [Traversing Chains](https://wiki.archlinux.org/title/Iptables#Traversing_Chains)

> A network packet received on any interface traverses the traffic control chains of tables in the order shown in the flow chart. The 3 most commonly used targets are ACCEPT, DROP, and jump to a user-defined chain.

## 安装

安装 iptables ：

```bash
# apt-get install iptables
# iptables --version
iptables v1.6.0
```

打开 iptable\_nat 内核模块：

```bash
# lsmod | grep iptable
iptable_filter         16384  0
ip_tables              24576  1 iptable_filter
x_tables               36864  2 ip_tables,iptable_filter
# modprobe iptable_nat
# lsmod | grep iptable
iptable_nat            16384  0
nf_nat_ipv4            16384  1 iptable_nat
iptable_filter         16384  0
ip_tables              24576  2 iptable_filter,iptable_nat
x_tables               36864  2 ip_tables,iptable_filter
```

## 使用

# K8S

[Kubernetes: iptables proxy mode](https://kubernetes.io/docs/concepts/services-networking/service/#proxy-mode-iptables) 提到 kube-proxy 在 iptables proxy 模式下会利用 iptable 工作：

> For each Service, it installs iptables rules, which capture traffic to the Service's clusterIP and port, and redirect that traffic to one of the Service's backend sets. For each Endpoint object, it installs iptables rules which select a backend Pod.

本文会探索 Kubernetes 如何利用 iptables 以达到路由流量的目的。

```bash
# iptables -L
Chain INPUT (policy ACCEPT)
target     prot opt source               destination

Chain FORWARD (policy ACCEPT)
target     prot opt source               destination

Chain OUTPUT (policy ACCEPT)
target     prot opt source               destination
```

# 参考资料

+ [CentOS: Iptables](https://wiki.centos.org/HowTos/Network/IPTables)
+ [](https://ipset.netfilter.org/iptables.man.html)
+ [Arch Linux Wiki: iptables](https://wiki.archlinux.org/title/Iptables)
+ [Kubernetes: iptables proxy mode](https://kubernetes.io/docs/concepts/services-networking/service/#proxy-mode-iptables)
