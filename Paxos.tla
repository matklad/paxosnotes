---- MODULE Paxos ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Value, Acceptor, Quorum

perms == Permutations(Acceptor)

Ballot == 0..2

VARIABLE msgs, maxBal, maxVBal

Send(m) == msgs' = msgs \cup {m}

Phase1a(b) ==
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal>>

Phase1b(a) ==
    \E m \in msgs:
        /\ m.type = "1a" /\ maxBal[a] < m.bal
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal - 1]
        /\ Send([type |-> "1b",
                 acc |-> a,
                 bal |-> m.bal,
                 vbal |-> maxVBal[a]])
        /\ UNCHANGED <<maxVBal>>

Phase2a(b, v) ==
    /\ ~\E m \in msgs: m.type = "2a" /\ m.bal = b
    /\ \E q \in Quorum:
        LET
            Q1b == { m \in msgs: m.type = "1b" /\ m.acc \in q /\ m.bal = b }
            Q1bv == { m \in Q1b: m.vbal[1] >= 0 }
        IN
          /\ \A a \in q: \E m \in Q1b: m.acc = a
          /\ \/ Q1bv = {}
             \/ \E m \in Q1bv:
                /\ m.vbal[2] = v
                /\ \A mm \in Q1bv: m.vbal[1] >= mm.vbal[1]
          /\ Send([type |-> "2a", bal |-> b, val |-> v])
          /\ UNCHANGED <<maxBal, maxVBal>>

Phase2b(a) ==
    \E m \in msgs:
        /\ m.type = "2a" /\ maxBal[a] < m.bal
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = <<m.bal, m.val>>]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Init ==
    /\ msgs = {}
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> << -1, -1 >>]

Next ==
    \/ \E b \in Ballot:
        \/ Phase1a(b)
        \/ \E v \in Value: Phase2a(b, v)
    \/ \E a \in Acceptor:
        \/ Phase1b(a)
        \/ Phase2b(a)

chosen == {v \in Value: \E q \in Quorum, b \in Ballot: \A a \in q:
          [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs}

TypeOK ==
    /\ msgs \subseteq  ([type: {"1a"}, bal: Ballot]
                        \cup [type: {"1b"}, bal: Ballot, acc: Acceptor, vbal: (Ballot \cup {-1}) \X (Value \cup {-1})]
                        \cup [type: {"2a"}, bal: Ballot, val: Value]
                        \cup [type: {"2b"}, bal: Ballot, val: Value, acc: Acceptor])
    /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVBal \in [Acceptor -> (Ballot \cup {-1}) \X (Value \cup {-1})]
    /\ \A v1, v2 \in chosen: v1 = v2
    \* /\ chosen = {}
====
