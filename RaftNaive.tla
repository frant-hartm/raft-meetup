----------------------------- MODULE RaftNaive -----------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC



CONSTANTS Server
CONSTANTS Value
CONSTANTS Follower, Candidate, Leader
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

VARIABLE messages

VARIABLE currentTerm
VARIABLE state
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>

VARIABLE votesResponded
VARIABLE votesGranted
candidateVars == <<votesResponded, votesGranted>>

vars == <<messages, serverVars, candidateVars>>

Quorum == {servers \in SUBSET(Server) : Cardinality(servers) > (Cardinality(Server) \div 2)}

\* TODO check if I use these

Send(m) == messages' = messages \union {m}
Discard(m) == messages' = messages \ {m}
Reply(response, request) == messages' = (messages \ {request}) \union {response}

InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> {}]

InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]

Init == /\ messages = {}
        /\ InitServerVars
        /\ InitCandidateVars

Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ votedFor'       = [votedFor EXCEPT ![i] = {}]    
    /\ UNCHANGED <<messages, currentTerm>>

Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              /\ votedFor' = [votedFor EXCEPT ![i] = {i}]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}]
              /\ UNCHANGED <<messages>>


RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ i # j
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars>>

BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars>>


HandleRequestVoteRequest(i, j, m) ==
    LET grant == /\ m.mterm = currentTerm[i]
                 /\ votedFor[i] = {j} \/ votedFor[i] = {}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars>>

HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.\
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor>>

UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = {}]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars>>

DropStaleResponse(i, j, m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars>>

Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)       

\* todo delete this if not performant
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars>>

DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars>>

Next == \/ \E i \in Server : Timeout(i)
        \/ \E i,j \in Server : RequestVote(i, j)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server : Restart(i)
        \/ \E m \in messages : Receive(m)
        \/ \E m \in messages : DuplicateMessage(m)        
        \/ \E m \in messages : DropMessage(m)

BothLeader( i, j ) == 
    /\ i /= j
    /\ currentTerm[i] = currentTerm[j]
    /\ state[i] = Leader
    /\ state[j] = Leader

SingleLeader ==
    \A i, j \in Server :  ~BothLeader( i, j ) 

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ SF_vars(Next)

=============================================================================
\* Modification History
\* Last modified Tue Feb 25 23:11:42 CET 2020 by frantisek
\* Created Mon Feb 24 10:05:48 CET 2020 by frantisek
