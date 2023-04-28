---
layout: post
title: Jenkins On K8S
date: 2021-11-21 12:17:48
tags:
  - [Computer Science, Tools, CD]
---

# 通过 Helm 在 K8S 上安装 Jenkins

## 什么是 Helm ？

[Helm](https://helm.sh) 是 K8S 上的包管理器，负责安装和升级复杂 K8S 软件。以 HDFS 为例，配置 HDFS 集群是非常繁琐的：

+ 启动 ZooKeeper ；
+ 启动 Journal Nodes ；
+ 启动 Name Nodes ；
+ 启动 Data Nodes 。

且各步骤之间存在依赖关系，单靠 K8S 无法表述如此复杂的安装过程，所以就有了 Helm 。[apache-spark-on-k8s/kubernetes-HDFS](https://github.com/apache-spark-on-k8s/kubernetes-HDFS/blob/master/charts/README.md) 就利用 Helm 在 K8S 上安装了 HDFS 。

## 准备镜像

我们将会在局域网环境构建 Jenkins ，无法从公网下载镜像，所以需要推送镜像到内部镜像仓库。

本篇文章以[阿里云容器镜像服务 ACR](https://help.aliyun.com/product/60716.html)作为内部镜像仓库：

|           公网镜像            |                                  公网 ACR                                   |                                     VPC ACR                                     |   备注   |
|              :-:              |                                     :-:                                     |                                       :-:                                       |   :-:    |
| jenkins/jenkins:2.303.3-jdk11 | registry.cn-hangzhou.aliyuncs.com/myjenkins-x/jenkins-jenkins:2.303.3-jdk11 | registry-vpc.cn-hangzhou.aliyuncs.com/myjenkins-x/jenkins-jenkins:2.303.3-jdk11 | 预装插件 |
|  kiwigrid/k8s-sidecar:1.14.2  |  registry.cn-hangzhou.aliyuncs.com/myjenkins-x/kiwigrid-k8s-sidecar:1.14.2  |  registry-vpc.cn-hangzhou.aliyuncs.com/myjenkins-x/kiwigrid-k8s-sidecar:1.14.2  |          |
| jenkins/inbound-agent:4.11-1  | registry.cn-hangzhou.aliyuncs.com/myjenkins-x/jenkins-inbound-agent:4.11-1  | registry-vpc.cn-hangzhou.aliyuncs.com/myjenkins-x/jenkins-inbound-agent:4.11-1  |          |
|    maorfr/kube-tasks:0.2.0    |    registry.cn-hangzhou.aliyuncs.com/myjenkins-x/maorfr-kube-tasks:0.2.0    |    registry-vpc.cn-hangzhou.aliyuncs.com/myjenkins-x/maorfr-kube-tasks:0.2.0    |          |

```Dockerfile
# registry.cn-hangzhou.aliyuncs.com/myjenkins-x/jenkins-jenkins:2.303.3-jdk11
FROM jenkins/jenkins:2.303.3-jdk11
RUN /usr/local/bin/install-plugins.sh \
  kubernetes                          \
  configuration-as-code               \
  workflow-aggregator                 \
  blueocean
```

## 创建 K8S 集群

本篇文章使用阿里云容器服务 ACK 帮忙创建 K8S 集群。

```bash
# wget https://github.com/jenkinsci/helm-charts/releases/download/jenkins-3.8.8/jenkins-3.8.8.tgz
# helm install jenkins jenkins-3.8.8.tgz
```

## 创建 storage class

![](http://junbin-hexo-img.oss-cn-beijing.aliyuncs.com/jenkins-on-k8s/cloud-essd-sc.png)

```bash
# kubectl describe sc cloud-essd-sc
kubectl describe sc cloud-essd-sc
Name:                  cloud-essd-sc
IsDefaultClass:        No
Annotations:           <none>
Provisioner:           diskplugin.csi.alibabacloud.com
Parameters:            type=cloud_essd
AllowVolumeExpansion:  True
MountOptions:          <none>
ReclaimPolicy:         Delete
VolumeBindingMode:     Immediate
Events:                <none>
```

## 准备 jenkins-values.yaml

以 [jenkinsci/helm-charts/values.yaml](https://raw.githubusercontent.com/jenkinsci/helm-charts/f53998b5fe45f7b13a21f28797e0fb0bc61fd77e/charts/jenkins/values.yaml) 为例，修改以下几项：

+ image
+ pv

```bash
# cat jenkins-values.yaml.patch
21,23c21,23
<   image: "jenkins/jenkins"
<   # tag: "2.303.3-jdk11"
<   tagLabel: jdk11
---
>   image: "registry-vpc.cn-hangzhou.aliyuncs.com/myjenkins-x/jenkins-jenkins"
>   tag: "2.303.3-jdk11"
>   # tagLabel: jdk11
231,235c231
<   installPlugins:
<     - kubernetes:1.30.1
<     - workflow-aggregator:2.6
<     - git:4.9.0
<     - configuration-as-code:1.53
---
>   installPlugins: []
249c245
<   initializeOnce: false
---
>   initializeOnce: true
339c335
<       image: kiwigrid/k8s-sidecar:1.14.2
---
>       image: registry-vpc.cn-hangzhou.aliyuncs.com/myjenkins-x/kiwigrid-k8s-sidecar:1.14.2
580c576
<   image: "jenkins/inbound-agent"
---
>   image: "registry-vpc.cn-hangzhou.aliyuncs.com/myjenkins-x/jenkins-inbound-agent"
753c749
<   storageClass:
---
>   storageClass: "cloud-essd-sc"
757c753
<   size: "8Gi"
---
>   size: "20Gi"
828c824
<     repository: "maorfr/kube-tasks"
---
>     repository: "registry-vpc.cn-hangzhou.aliyuncs.com/myjenkins-x/maorfr-kube-tasks"
```

```bash
# cp values.yaml jenkins-values.yaml
# patch jenkins-values.yaml < jenkins-values.yaml.patch
patching file jenkins-values.yaml
```

## 安装 Jenkins

```bash
# kubectl create namespace jenkins
namespace/jenkins created
# helm install jenkins /tmp/jenkins-3.8.8.tgz -f jenkins-values.yaml -n jenkins
NAME: jenkins
LAST DEPLOYED: Sun Nov 21 22:33:21 2021
NAMESPACE: jenkins
STATUS: deployed
REVISION: 1
NOTES:
1. Get your 'admin' user password by running:
  kubectl exec --namespace jenkins -it svc/jenkins -c jenkins -- /bin/cat /run/secrets/chart-admin-password && echo
2. Get the Jenkins URL to visit by running these commands in the same shell:
  echo http://127.0.0.1:8080
  kubectl --namespace jenkins port-forward svc/jenkins 8080:8080
3. Login with the password from step 1 and the username: admin
4. Configure security realm and authorization strategy
5. Use Jenkins Configuration as Code by specifying configScripts in your values.yaml file, see documentation: http:///configuration-as-code and examples: https://github.com/jenkinsci/configuration-as-code-plugin/tree/master/demos
For more information on running Jenkins on Kubernetes, visit:
https://cloud.google.com/solutions/jenkins-on-container-engine
For more information about Jenkins Configuration as Code, visit:
https://jenkins.io/projects/jcasc/
```

# Reference

[Helm](https://helm.sh)
[apache-spark-on-k8s/kubernetes-HDFS](https://github.com/apache-spark-on-k8s/kubernetes-HDFS)
[Jenkins Handbook](https://www.jenkins.io/doc/book)
