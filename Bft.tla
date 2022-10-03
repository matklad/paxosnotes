---- MODULE Bft ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Value, Acceptor, EAcceptor, Quorum, WQuorum

perms1 == Permutations(Acceptor) \cup Permutations(Value)


Ballot == 0..2

VARIABLE msgs, maxBal, maxVBal, confirm

Send(m) == msgs' = msgs \cup {m}

Confirmed(b, v) ==
    \E q \in Quorum: \A a \in q: [type |-> "2ac", bal |-> b, val |-> v, acc |-> a] \in msgs

Byzantine(a) ==
    /\  \/  \E b \in Ballot: Send([type |-> "1a", bal |-> b])
        \/  \E b \in Ballot, v \in Value: Send([type |-> "2a", bal |-> b, val |-> v ])
        \/  \E b1 \in Ballot, b2 \in Ballot, v \in Value: b2 < b1 /\ Send([type |-> "1b", bal |-> b1, acc |-> a, vbal |-> <<b2, v>> ])
        \/  \E b \in Ballot, v \in Value: Send([type |-> "2ac", bal |-> b, val |-> v, acc |-> a ])
        \* \/  \E b \in Ballot, v \in Value: Send([type |-> "2b", bal |-> b, val |-> v, acc |-> a ])
    /\ UNCHANGED <<maxBal, maxVBal, confirm>>


Phase1b(a) ==
    \E m \in msgs:
        /\ m.type = "1a" /\ maxBal[a] < m.bal
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal - 1]
        /\ Send([type |-> "1b",
                 acc |-> a,
                 bal |-> m.bal,
                 vbal |-> maxVBal[a]])
        /\ UNCHANGED <<maxVBal, confirm>>


Phase2ac(a) ==
    \E m2a \in msgs:
        /\ m2a.type = "2a" /\ confirm[a][m2a.bal] = -1
        /\ \E q \in Quorum:
             LET
                 Q1b == { m \in msgs: m.type = "1b" /\ m.acc \in q /\ m.bal = m2a.bal }
                 Q1bv == { m \in Q1b: m.vbal[1] >= 0 }
             IN
               /\ \A aa \in q: \E m \in Q1b: m.acc = aa
               /\ \/ Q1bv = {}
                  \/ \E m \in Q1bv:
                     /\ m.vbal[2] = m2a.val
                     /\ \A mm \in Q1bv: m.vbal[1] >= mm.vbal[1]
                     /\ \E aa \in WQuorum: [type |-> "2ac", bal |-> m.vbal[1], val |-> m.vbal[2], acc |-> aa] \in msgs
        /\ Send([type |-> "2ac", bal |-> m2a.bal, val |-> m2a.val, acc |-> a])
        /\ confirm' = [confirm EXCEPT ![a] = [confirm[a] EXCEPT ![m2a.bal] = m2a.val]]
        /\ UNCHANGED <<maxBal, maxVBal>>


Phase2b(a) ==
    /\ \E b \in Ballot, v \in Value:
          /\ maxBal[a] < b
          /\ Confirmed(b, v)
          /\ maxBal' = [maxBal EXCEPT ![a] = b]
          /\ maxVBal' = [maxVBal EXCEPT ![a] = <<b, v>>]
          /\ Send([type |-> "2b", acc |-> a, bal |-> b, val |-> v])
    /\ UNCHANGED <<confirm>>

Init ==
    /\ msgs = {}
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> << -1, -1 >>]
    /\ confirm = [a \in Acceptor |-> [b \in Ballot |-> -1] ]

Next ==
    \/ \E a \in Acceptor:
        \/ Phase1b(a)
        \/ Phase2ac(a)
        \/ Phase2b(a)
    \/ \E a \in EAcceptor: Byzantine(a)

chosen == {v \in Value: \E q \in Quorum, b \in Ballot: \A a \in q:
          [type |-> "2b", acc |-> a, bal |-> b, val |-> v] \in msgs}

TypeOK ==
    /\ msgs \subseteq  ([type: {"1a"}, bal: Ballot]
                        \cup [type: {"1b"}, bal: Ballot, acc: (EAcceptor \cup Acceptor), vbal: (Ballot \cup {-1}) \X (Value \cup {-1})]
                        \cup [type: {"2a"}, bal: Ballot, val: Value]
                        \cup [type: {"2ac"}, bal: Ballot, val: Value, acc: (EAcceptor \cup Acceptor)]
                        \cup [type: {"2b"}, bal: Ballot, val: Value, acc: (EAcceptor \cup Acceptor)])
    /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVBal \in [Acceptor -> (Ballot \cup {-1}) \X (Value \cup {-1})]
    /\ confirm \in [Acceptor -> [Ballot -> Value \cup {-1}]]
    /\ \A v1, v2 \in chosen: v1 = v2
    \* /\ chosen = {}
====
