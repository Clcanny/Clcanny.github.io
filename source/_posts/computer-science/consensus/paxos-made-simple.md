Every acceptor in C has accepted a proposal with number in
m . .(n − 1), and every proposal with number in m . .(n − 1)
accepted by any acceptor has value v.
[m, n - 1) 因为 C 里面的成员都给 m 投过票，这条规则是 trivial 的。

p2c 为什么能推出 p2b ？

https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2005-112.pdf

https://lamport.azurewebsites.net/tla/paxos-algorithm.html
https://matklad.github.io/2020/11/01/notes-on-paxos.html

https://stackoverflow.com/questions/3340383/what-is-the-proper-behaviour-for-a-paxos-agent-in-this-scenario
It has been a while :) I accepted your answer because of the phrase "the choice is made as soon as a majority receives an accept!(n, v) message which they have not promised to ignore". That's key. The Paxos protocol is 'complete' as soon as a majority of acceptors accept a value. The Commit (or Decide) is simply an optimization in which a distinguished learner (i.e. the proposer) broadcasts the consensus to all interested learners. You could do skip the Commit by having each Acceptor broadcast their vote to all learners. This is stated in "Paxos Made Simple", though it's easy to overlook.
