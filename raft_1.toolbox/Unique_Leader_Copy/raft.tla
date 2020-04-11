--------------------------------- MODULE raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* Server states.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

\* Maximum number of client requests
CONSTANTS MaxClientRequests



----
\* Global variables



\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of successful elections, including the initial logs of the
\* leader and voters' logs. Set of functions containing various things about
\* successful elections (see BecomeLeader).
VARIABLE elections

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Keeps track of every log ever in the system (set of logs).
VARIABLE allLogs

\* save every log of every server
VARIABLE oldLogs

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor

\* the sequence of currentTerm for every server
VARIABLE currentTermList

serverVars == <<currentTerm, currentTermList, state, votedFor>>

\* The set of requests that can go into the log
VARIABLE clientRequests

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
\* The index that gets committed
VARIABLE committedLog
\* Does the commited Index decrease
VARIABLE committedLogDecrease
logVars == <<log, oldLogs, commitIndex, clientRequests, committedLog, committedLogDecrease >>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesSent
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog
candidateVars == <<votesSent, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex, elections>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, allLogs, serverVars, candidateVars, leaderVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE
        msgs

ValidMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] > 0 }

SingleMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] = 1 } 

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitHistoryVars == /\ elections = {}
                   /\ allLogs   = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
                   /\ oldLogs   = [i \in Server |-> <<>>]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
                  /\ currentTermList = [i \in Server |-> <<>>]
InitCandidateVars == /\ votesSent = [i \in Server |-> FALSE ]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
               /\ clientRequests = 1
               /\ committedLog = << >>
               /\ committedLogDecrease = FALSE
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesSent'      = [votesSent EXCEPT ![i] = FALSE ]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, currentTermList, votedFor, log, oldLogs, elections, clientRequests, committedLog, committedLogDecrease>>

\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              /\ currentTermList' = [currentTermList EXCEPT ![i] = Append(currentTermList[i], currentTerm[i] + 1)]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesSent' = [votesSent EXCEPT ![i] = FALSE ]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars>>

\* Candidate i sends j a RequestVote request.
RequestVote(i,j) ==
    /\ state[i] = Candidate
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, votesGranted, voterLog, leaderVars, logVars, votesSent>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN Send([mtype          |-> AppendEntriesRequest,
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
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ elections'  = elections \cup
                         {[eterm     |-> currentTerm[i],
                           eleader   |-> i,
                           elog      |-> log[i],
                           evotes    |-> votesGranted[i],
                           evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, currentTerm, currentTermList, votedFor, candidateVars, logVars>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ clientRequests < MaxClientRequests
    /\ LET entry == [term  |-> currentTerm[i],
                     value |-> clientRequests]
           newLog == Append(log[i], entry)
       IN  /\ log' = [log EXCEPT ![i] = newLog]
            /\ oldLogs' = [oldLogs EXCEPT ![i] = Append(oldLogs[i], log[i])]
           \* Make sure that each request is unique, reduce state space to be explored
           /\ clientRequests' = clientRequests + 1
    /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, committedLog, committedLogDecrease>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           newCommittedLog ==
              IF newCommitIndex > 1 THEN 
                  [ j \in 1..newCommitIndex |-> log[i][j] ] 
              ELSE 
                   << >>
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ committedLogDecrease' = \/ ( newCommitIndex < Len(committedLog) )
                                     \/ \E j \in 1..Len(committedLog) : committedLog[j] /= newCommittedLog[j]
          /\ committedLog' = newCommittedLog
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, oldLogs, clientRequests>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, currentTermList, candidateVars, leaderVars, logVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
          /\ UNCHANGED <<votesSent>>
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesSent, votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
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
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, currentTermList, votedFor, logVars, messages>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, logVars>>
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
                                          log[i][index2]]
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                        /\ oldLogs' = [oldLogs EXCEPT  ![i] = Append(oldLogs[i], log[i])]
                       /\ UNCHANGED <<serverVars, commitIndex, messages, clientRequests, committedLog, committedLogDecrease>>
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>

\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ currentTermList' = [currentTermList EXCEPT ![i] = Append(currentTermList[i], m.mterm)]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Receive a message.
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

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Defines how the variables may transition.
Next == /\ \/ \E i \in Server : Restart(i)
           \/ \E i \in Server : Timeout(i)
           \/ \E i, j \in Server : RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \/ \E i \in Server : ClientRequest(i)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : AppendEntries(i, j)
           \/ \E m \in ValidMessage(messages) : Receive(m)
           \/ \E m \in SingleMessage(messages) : DuplicateMessage(m)
           \/ \E m \in ValidMessage(messages) : DropMessage(m)
           \* History variable that tracks every log ever:
        /\ allLogs' = allLogs \cup {log[i] : i \in Server}

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

\* The following are a set of verification by jinlmsft@hotmail.com
BothLeader( i, j ) == 
    /\ i /= j
    /\ currentTerm[i] = currentTerm[j]
    /\ state[i] = Leader
    /\ state[j] = Leader

MoreThanOneLeader ==
    \E i, j \in Server :  BothLeader( i, j )
    
    
\* Lemma 1. Each server's currentTerm monotonically increases:
\* \A i \in Server : currentTerm[i] <= currentTerm'[i]
Lemma1CurrentTermIncrease == \A i \in Server : \/ Len(currentTermList[i]) \in {0,1}
                                         \/ /\ Len(currentTermList[i]) > 1
                                            /\ \A j \in (2 .. Len(currentTermList[i])) : 
                                                currentTermList[i][j - 1] <= currentTermList[i][j]

\* Lemma 2. There is at most one leader per term:
\* \A e,f \in  elections :
\*      (e.eterm = f.eterm ) => (e.eleader = f.eleader)
\* This is the Election Safety property.
Lemma2AtMostOneLeader == \A e,f \in elections:
                        (e.eterm = f.eterm ) => (e.eleader = f.eleader)

\* Lemma 3. A leader's log monotonically grows during its term:
\* \A e \in elections :
\*      currentTerm[e.leader] = e.term =>
\*      \A index \in 1 .. Len(log[e.leader]) :
\*      log'[e.leader][index] = log[e.leader][index]
\* This is the Leader Append-Only property.
Lemma3LeaderLogGrow == \A e \in elections:
        (currentTerm[e.eleader] = e.eterm) => 
            (
                LET oldLog == \* last log of e.eleader
                    (
                        IF Len(oldLogs[e.eleader]) = 0 THEN 
                                <<>>
                        ELSE 
                                oldLogs[e.eleader][Len(oldLogs[e.eleader])]
                    ) 
                IN
                    \* /\ state[e.eleader] = Leader
                    /\ Len(oldLog) <= Len(log[e.eleader])
                    /\ \/ Len(oldLog) = 0
                        \/ \A i \in (1 .. Len(oldLog)) : oldLog[i] = log[e.eleader][i]
            )

\* Lemma 4. An <<index, term>> pair identifies a log prefix:
\* \A l, m \in allLogs :
\*    \A <<index, term>> \in l :
\*       <<index, term>> \in m =>
\*       \A pindex \in 1 .. index:
\*          l[pindex] = m[pindex]
\* This is the Log Matching property.
Lemma4LogPrefixMatch == \A l,m \in allLogs: 
        \A index \in (1 .. Min({Len(l),Len(m)})): 
            (l[index].term = m[index].term) =>
                (\A j \in (1 .. index) : l[j].term = m[j].term)

\* Lemma 5. When a follower appends an entry to its log, its log after the append is a prefix of the
\* leader's log at the time the leader sent the AppendEntries request:
\* \A i \in Server :
\*      state[i] /= Leader /\ Len(log'[i]) > Len(log[i]) =>
\*          \E m \in DOMAIN messages :
\*              /\ m.mtype = AppendEntriesRequest
\*              /\ \A index \in (1 .. Len(log'[i])):
\*                  log'[i][index] = m.mlog[index]
Lemma5FollowerLogIsPrefixOfLeader ==
        \A i \in Server:
            (state[i] /= Leader /\ Len(oldLogs[i]) < Len(log[i])) =>
            (
                \E m \in DOMAIN messages:
                    /\ m.mtype = AppendEntriesRequest
                    /\ \A index \in (1 .. Len(log[i])) : 
                        log[i][index] = m.mlog[index]
            )

\* Lemma 6. A server's current term is always at least as large as the terms in its log:
\* \A i \in Server :
\*      \A <<index, term>> \in log[i]:
\*          term <= currentTerm[i]
Lemma6CurrentTermAtLeastAsLargeAsTermsInLog ==
        \A i \in Server:
            \A index \in (1 .. Len(log[i])): log[i][index].term <= currentTerm[i]

\* Lemma 7. The terms of entries grow monotonically in each log:
\* \A l \in allLogs :
\*      \A index \in (1 .. (Len(l) - 1)):
\*          l[index].term <= l[index +1].term
Lemma7TermGrowInLog == 
        \A l \in allLogs :
            \A index \in (1 .. (Len(l) - 1)):
                l[index].term <= l[index+1].term

\* Definition 1. An entry <<index,term> is committed at term t if it is present in every leader's log
\* following t :
\*      committed(t) == { <<index,term>> :
\*                          \A election \in elections :
\*                              election.eterm > t => <<index,term>> \in election.elog}
entriesInElectionLog(election) == {
    (
        <<index,election.elog[index].term>>
    ) : index \in (1 .. Len(election.elog))
}

committed(t) == {   (IF election.eterm > t THEN (
                                                LET entriesInElection == UNION entriesInElectionLog(election)
                                                IN (
                                                        IF Cardinality(entriesInElection) /= 0 THEN 
                                                            entriesInElection
                                                        ELSE <<0,0>>
                                                    )
                                                )
                    ELSE <<0,0>>
                    ): election \in elections
                }

\* Definition 2. An entry <<index,term>> is immediately committed if it is acknowledged by a quorum
\* (including the leader) during term. Lemma 8 shows that these entries are committed at term.
\* immediatelyCommitted == { <<index,term>> \in anyLog :
\*                              /\ anyLog \in allLogs
\*                              /\ \E leader \in Server, subquorum \in SUBSET Server :
\*                                  /\ subquorum \union {leader} \in Quorum
\*                                  /\ \A i \in subquorum :
\*                                      \E m \in messages :
\*                                          /\ m.mtype = AppendEntriesResponse
\*                                          /\ m.msource = i
\*                                          /\ m.mdest = leader
\*                                          /\ m.mterm = term
\*                                          /\ m.mmatchIndex >= index

\* validSubquorum == <<leader, subquorum>>
leaderTimesSubquorum == { x \in Server \times SUBSET Server  : ((x[2] \union {x[1]}) \in Quorum) }

entriesCommitted(leader,subquorum,m,index,term) == 
    {
        IF     /\ m.mtype = AppendEntriesResponse
                /\ m.msource = i
                /\ m.mdest = leader
                /\ m.mterm = term
                /\ m.mmatchIndex >= index
        THEN <<index,term>>
        ELSE <<0,0>>
        : i \in subquorum
    }

committedSetOfAnyLog(anyLog) == 
    IF Cardinality(DOMAIN messages) = 0 \/ Len(anyLog) = 0 THEN 
        {}
    ELSE
        UNION {
            (
                entriesCommitted(x[1],x[2],m,index,anyLog[index].term)
            ) : x \in leaderTimesSubquorum, m \in DOMAIN messages, index \in (1 .. Len(anyLog))
        }

immediatelyCommitted == UNION {
                           committedSetOfAnyLog(anyLog) : anyLog \in allLogs
                        }

\* Lemma 8. Immediately committed entries are committed:
\* \A <<index,term>> \in immediatelyCommitted :
\*      <<index,term>> \in committed(term)
\* Along with Lemma 9, this is the Leader Completeness property
Lemma8ImmediatelyCommittedIsCommitted == 
    (
        IF Cardinality(immediatelyCommitted) /= 0 THEN 
            \A x \in immediatelyCommitted: 
                IF x = <<0,0>> THEN \* x is <<0,0>>,so it is committed
                    TRUE
                ELSE 
                (
                    LET cset == committed(x[2])
                    IN (
                        \* there is only <<0,0>> in cset. it means actually cset is empty set.
                        IF Cardinality(cset) = 1 /\ <<0,0>> \in cset THEN 
                            TRUE
                        ELSE IF Cardinality(cset) /= 0 THEN 
                            /\ Print(x,TRUE)
                            /\ Print(cset,TRUE) 
                            /\ x \in cset
                            \* TRUE
                        ELSE  TRUE
                    )
                )
        ELSE TRUE
    )

\* Definition 3. An entry <<index, term>> is prefix committed at term t if there is another entry that
\* is committed at term t following it in some log. Lemma 9 shows that these entries are committed at
\* term t .
\* prefixCommitted(t) == { <<index, term>> \in anyLog :
\*                          /\ anyLog \in allLogs
\*                          /\ \E <<rindex, rterm>> \in anyLog :
\*                              /\ index < rindex
\*                              /\ <<rindex,rterm>> \in committed(t) }

followingEntries(t,index,anyLog) ==
    IF Len(anyLog) = 0 \/ index >= Len(anyLog) THEN 
        {}
    ELSE 
        {
            (
                IF <<j,anyLog[j].term>> \in committed(t) THEN 
                    <<j,anyLog[j].term>>
                ELSE <<0,0>>
            )
            : j \in (index .. Len(anyLog))
        }

prefixCommittedSetOfAnyLog(t,anyLog) == 
    IF Len(anyLog) = 0 THEN 
        {}
    ELSE 
        UNION {
            (
                followingEntries(t,index+1,anyLog)
            ) : index \in (1 .. Len(anyLog))
        }

prefixCommitted(t) == UNION {
                        prefixCommittedSetOfAnyLog(t,anyLog) : anyLog \in allLogs
                    }

\* Lemma 9. Prefix committed entries are committed in the same term:
\* \A t : prexCommitted(t) \subseteq committed(t)
\* Along with Lemma 8, this is the Leader Completeness property
termSet == {currentTerm[i] : i \in Server}

Lemma9PrefixCommittedIsCommited == \A t \in (1 .. Max(termSet)) : prefixCommitted(t) \subseteq committed(t)

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
