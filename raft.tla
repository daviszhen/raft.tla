--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

----
\* Global variables

\* record包表示请求和应答。是Message到Nat的映射
\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

\* 记录成功的选举
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* 记录系统中的每个日志
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
VARIABLE allLogs

----
\* 每个server都有的变量
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor

\* serverVar 有序元组<currentTerm, state, votedFor>
serverVars == <<currentTerm, state, votedFor>>

\* 日志，entry数组
\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex

\* 有序元组<log, commitIndex>
logVars == <<log, commitIndex>>

\* 只在candidate上用的变量
\* The following variables are used only on candidates:

\* 在currentTerm期间，给candidate RV应答的server集合
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded

\* 在currentTerm期间，给candidate投票的server集合
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted

\* 在currentTerm期间，给candidate投票的server的日志,是个函数server -> voter的日志
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog

\* 有序元组 <votesResponded, votesGranted, voterLog>
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* 只在leader上用的变量
\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex

\* 有序元组 <nextIndex, matchIndex, elections>
leaderVars == <<nextIndex, matchIndex, elections>>

\* End of per server variables.
----

\* 用于结巴状态(断言状态不变)的所有变量
\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars>>

----
\* Helpers

\* 所有quorum的集合。重要的特征是每个quorum与其它的会重叠
\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
\* SUBSET(Server) 表示 Server所有子集的集合，也就是Server的幂集. SUBSET是幂集运算符。
\* Cardinality(i) 表示集合i中的元素个数，如果集合i是有限集合。Cardinality是集合基数运算符。
\* Quorum定义为SUBSET(Server)的子集，即Server集合幂集的子集，
\* 这些子集满足条件：Cardinality(i) * 2 > Cardinality(Server)
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* log中最后一个entry的term。如果log是空，返回0
\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* 发送和应答的帮助函数。给定messge m和message包，返回message的新包，新包多了个m。
\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
\* 如果m 在 msgs的定义域中，新msgs是 msgs中m计数增加1
\* 否则，新msgs是 msgs加上 m，即新msgs[m]=1
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* 丢弃和应答帮助函数。给定message m和message包，返回message的新包，新包少了m。
\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\* 如果m 在 msgs的定义域中，新msgs是 msgs中m计数减少1
\* 否则，msgs不变。
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* 定义运算符Send(m)
\* messages在下个状态的值 等于 messages增加m
\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* 定义运算符Discard(m)
\* messages在下个状态的值 等于 messages删除m
\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* 定义运算符Reply(response, request)
\* messages在下个状态的值 等于 messages增加response，再删除request
\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* 定义运算符Min(S)，返回集合s的最小值。如果集合为空，无定义
\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* 定义运算符Max(S)，返回集合s的最大值。如果集合为空，无定义
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

\* elections和allLogs的初始值为空集
\* voterLog初始值为函数f[i] = 空序列，当i在Server中。
\* [j \in {} |-> <<>>]定义了个空序列。
InitHistoryVars == /\ elections = {}
                   /\ allLogs   = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]

\* currentTerm 初始值为函数f[i] = 1，当i在Server中
\* state 初始值为函数f[i] = Follower，当i在Server中
\* votedFor 初始值为函数f[i] = Nil，当i在Server中
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]

\* votesResponded初始值为函数f[i] = 空集，当i在Server中
\* votesGranted初始值为函数f[i] = 空集，当i在Server中
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]

\* nextIndex初始值为函数f[i][j] = 1，当i,j在Server中
\* matchIndex初始值为函数f[i][j] = 0，当i,j在Server中
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]

\* log初始值为函数f[i] = 空序列，当i在Server中
\* commitIndex初始值为函数f[i] = 0，当i在Server中
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]

\* messages初始值为函数f[i] = 0，当i在Server中 ????
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* 定义状态转移
\* Define state transitions

\* 定义Restart(i)运算符
\* Server i 从稳定存储中重启，除了currentTerm,votedFor和log外，其它东西都丢了
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower] \* state[i]=Follower
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]  \* votesResponded[i]=空集
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]    \* votesGranted[i]=空集
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]   \* voterLog[j]=空序列
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]] \* nextIndex[i][j]=1
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]    \* matchIndex[i][j]=0
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]  \* commitIndex[i]=0
    \* 元组<messages, currentTerm, votedFor, log, elections>保持不变
    /\ UNCHANGED <<messages, currentTerm,votedFor,log, elections>>

\* 定义Timeout(i)运算符
\* Server i 超时 并且 开始一个新的选举
\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate} \* state[i] = Follower或Candidate
              /\ state' = [state EXCEPT ![i] = Candidate]   \* state[i] = Candidate
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]  \* currentTerm[i]增加1
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]   \* votedFor[i] = Nil
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]    \* votesResponded[i] = 空集
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]  \* votesGranted[i] = 空集
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]] \* voterLog[i] = 空序列
            \* 元组<messages, leaderVars, logVars>保持不变
              /\ UNCHANGED <<messages, leaderVars, logVars>>

\* 定义RequestVote(i, j)运算符
\* Candidate i给j发送RequestVote request
\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate \* state[i] = Candidate
    /\ j \notin votesResponded[i]   \* j 不在votesResponded[i]中，即还未收到j的应答
    /\ Send([mtype         |-> RequestVoteRequest,\* 发送AV request，实际上是个Record
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    \* 元组<serverVars, candidateVars, leaderVars, logVars>保持不变
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* 定义AppendEntries(i, j)运算符
\* Leader i给j发送一个AE request，包含1个entry。
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j   \* i != j
    /\ state[i] = Leader    \* state[i] = Leader
    \* 定义变量prevLogIndex,prevLogTerm,lastEntry,entries
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           \* lastEntry是索引，Len(log[i]), nextIndex[i][j]中的最大值
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           \* entries 是log[i]中索引区间[nextIndex[i][j], lastEntry]中的Entry
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN Send([mtype          |-> AppendEntriesRequest,    \* 发送AE request，实际上是个Record
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
    \* 元组<serverVars, candidateVars, leaderVars, logVars>保持不变
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* 定义BecomeLeader(i)运算符
\* Candidate i transitions to leader.
\* Candidate i 转化为leader
BecomeLeader(i) ==
    /\ state[i] = Candidate \* state[i]当前是Candidate
    /\ votesGranted[i] \in Quorum   \*投票数够majority
    /\ state'      = [state EXCEPT ![i] = Leader]   \* state[i]下个值是Leader
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =   \* nextIndex[i][j]会变为Len(log[i])+1
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =  \* matchIndex[i][j]会变为0
                         [j \in Server |-> 0]]
    /\ elections'  = elections \cup \* elections会增加一个选举Record，包含了server i的日志，投票情况和投票者的日志
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],    \* server i的日志
                           evotes    |-> votesGranted[i],   \* 投票情况
                           evoterLog |-> voterLog[i]]}  \* 投票者的日志
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>

\* 定义ClientRequest(i, v)运算符
\* Leader i receives a client request to add v to the log.
\* Leader i 接收了一个client 请求(添加v到日志)
ClientRequest(i, v) ==
    /\ state[i] = Leader    \* 只有leader能接收请求
    /\ LET entry == [term  |-> currentTerm[i],  \* 新Entry<currentTerm[i],v>
                     value |-> v]
           newLog == Append(log[i], entry)  \* leader拼接entry到日志
       IN  log' = [log EXCEPT ![i] = newLog]    \* log[i]变为newLog
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex>>

\* 定义AdvanceCommitIndex(i)运算符
\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\* Leader i 推进 commitIndex
\* 这是与处理AE 响应分开的单独step，部分为了减少atomic region，部分为了single-server的leader能
\* 提交entries.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader    \* Leader才做
    /\ LET \* The set of servers that agree up through index.
            \* Agree(index)是集合，定义为 i 和 所有matchIndex[i][k] >= index的Server k。
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           \* agreeIndexes是集合，定义为 满足majority的index的集合。
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}  \* 必须要有满足majority的index
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i] \* 满足majority的index的最大值的term 必须是currentTerm[i]，即Leader只提交当前任期的日志
              THEN
                  Max(agreeIndexes) \* 满足majority的index的最大值，要么如下不变
              ELSE
                  commitIndex[i] 
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex] \* commitIndex[i]变为newCommitIndex
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* 定义HandleRequestVoteRequest(i, j, m)运算符
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* Server i 收到 来自 Server j的RV request，RV request中的m.mterm <= currentTerm[i].
\* m.mterm > currentTerm[i] ?
HandleRequestVoteRequest(i, j, m) ==
    \* logOk表示j的日志是否至少与i的日志一样新。日志比较基于两个条件。
    \* grand表示i是否给j投票。term相同是一个条件。logOk是一个条件。i要么给j投过票，要么没投过票，也是一个条件。
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])   \* 条件1：j的lastLogTerm 比 i的lastLogTerm大
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])    \* 条件2：当j的lastLogTerm 与 i的lastLogTerm相等时，j的lastLogIndex >= i的日志的长度
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]   \* 投票，votedFor[j]变为j
          \/ ~grant /\ UNCHANGED votedFor   \* 不投票，votedFor不变
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,    \* 投票情况
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],   \* 投票时,i的日志
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>

\* 定义HandleRequestVoteResponse(i, j, m)运算符
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
\* Server i 接收Server j的AV 应答,且m.mterm = currentTerm[i]
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}] \* votesResponded[i]新增j的应答
    /\ \/ /\ m.mvoteGranted \* j投票
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}] \* votesGranted[i]新增j的投票
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)] \* 新增voterLog[j]为m.mlog
       \/ /\ ~m.mvoteGranted \* j没投票，啥也不用动
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)   \* 丢弃m
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>

\* 定义HandleAppendEntriesRequest(i, j, m)运算符
\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
\* Server i 接收Server j的AE request，带上m.mterm <= currentTerm[i].
HandleAppendEntriesRequest(i, j, m) ==
    \* logOk表示prevLogTerm与log[i][prevLogIndex]匹配的情况
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \* 拒绝请求。
                \/ m.mterm < currentTerm[i] \* term < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]  \* 日志不匹配
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
            \* candidate转为follower
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower] \* state[i] = Follower
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept request
            \* 接受请求
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk   \* 日志匹配
             /\ LET index == m.mprevLogIndex + 1 \* index就是请求中的entry所在的index，下面要检测index处term的匹配情况。
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >> \* entries为空，heartbeat的情况
                          \/ /\ Len(log[i]) >= index    \* index在log[i]的范围内，并且index的term是匹配的。
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] = \* commitIndex[i]变为m.mcommitIndex
                                              m.mcommitIndex]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE, \* 日志匹配
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, logVars>>
                   \/ \* conflict: remove 1 entry
                        \* 冲突：删除1个entry
                       /\ m.mentries /= << >>   \* entries不为空
                       /\ Len(log[i]) >= index  \* index在log[i]范围内
                       /\ log[i][index].term /= m.mentries[1].term  \* index处的term不相等
                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->   \*  删掉log[i]尾部的entry
                                          log[i][index2]]
                          IN log' = [log EXCEPT ![i] = new] \*  log[i] = new
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
                   \/ \* no conflict: append entry
                        \* 无冲突:  拼接entry
                       /\ m.mentries /= << >>   \* entries不为空
                       /\ Len(log[i]) = m.mprevLogIndex \* prevLogIndex刚好为Len(log[i])
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]    \* log[i]拼接上entries[1]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* 定义HandleAppendEntriesResponse(i, j, m)运算符
\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
\* Server i 接收Server j的 AE 应答，且m.mterm = currentTerm[i]
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful，更新nextIndex和matchIndex
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]  \* nextIndex[i][j] = m.mmatchIndex + 1
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]  \* matchIndex[i][j] = m.mmatchIndex
       \/ /\ \lnot m.msuccess \* not successful，更新nextIndex
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]   \* nextIndex[i][j]减少
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)   \* 丢弃m
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>

\* 定义UpdateTerm(i, j, m)运算符
\* Any RPC with a newer term causes the recipient to advance its term first.
\* 当RPC请求中的term比currentTerm[i]大时，更新currentTerm[i]和其它状态
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]    \* 更新currentTerm[i]
    /\ state'          = [state       EXCEPT ![i] = Follower]   \* 更新state[i]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]        \* 更新votedFor[i]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

\* 定义DropStaleResponse(i, j, m)运算符
\* Responses with stale terms are ignored.
\* 丢弃过时的应答,即哪些来自之前term的应答
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)   \* 丢弃m
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* 定义Receive(m)运算符
\* Receive a message.
\* 接收j到i的消息
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* 定义DuplicateMessage(m)运算符
\* The network duplicates a message
\* 复制一个消息
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* 定义DropMessage(m)运算符
\* The network drops a message
\* 丢弃一个消息
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Defines how the variables may transition.
Next == /\ \/ \E i \in Server : Restart(i)
           \/ \E i \in Server : Timeout(i)
           \/ \E i,j \in Server : RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \/ \E i \in Server, v \in Value : ClientRequest(i, v)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : AppendEntries(i, j)
           \/ \E m \in DOMAIN messages : Receive(m)
           \/ \E m \in DOMAIN messages : DuplicateMessage(m)
           \/ \E m \in DOMAIN messages : DropMessage(m)
           \* History variable that tracks every log ever:
        /\ allLogs' = allLogs \cup {log[i] : i \in Server}

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* 检查选举安全性
BothLeader( i, j ) == 
    /\ i /= j
    /\ currentTerm[i] = currentTerm[j]
    /\ state[i] = Leader
    /\ state[j] = Leader

MoreThanOneLeader ==
    \E i, j \in Server :  BothLeader( i, j )

===============================================================================

\* Changelog:
\*
\* 2014-12-02:
\* - Fix AppendEntries to only send one entry at a time, as originally
\*   intended. Since SubSeq is inclusive, the upper bound of the range should
\*   have been nextIndex, not nextIndex + 1. Thanks to Igor Kovalenko for
\*   reporting the issue.
\* - Change matchIndex' to matchIndex (without the apostrophe) in
\*   AdvanceCommitIndex. This apostrophe was not intentional and perhaps
\*   confusing, though it makes no practical difference (matchIndex' equals
\*   matchIndex). Thanks to Hugues Evrard for reporting the issue.
\*
\* 2014-07-06:
\* - Version from PhD dissertation
