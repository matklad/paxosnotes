---- MODULE Ballot ----
EXTENDS Integers

CONSTANT Value, Acceptor, Quorum

Ballot == 0..3

VARIABLE votes, maxBal

Voted(a, b) ==
  \E v \in Value: <<a, b, v>> \in votes

Safe(v, b) ==
  \E q \in Quorum:
    /\ \A a \in q: maxBal[a] >= b - 1
    /\ \E b1 \in Ballot \cup {-1}:
        /\ \A b2 \in b1+1..b-1, a \in q: ~Voted(a, b2)
        /\ b1 = -1 \/ \E a \in q: <<a, b1, v>> \in votes

AdvanceMaxBal(a, b) ==
  /\ maxBal[a] < b
  /\ votes' = votes
  /\ maxBal' = [maxBal EXCEPT ![a] = b]

Vote(a, b, v) ==
  /\ maxBal[a] < b
  /\ \A vt \in votes: b = vt[2] => v = vt[3]
  /\ Safe(v, b)
  /\ votes' = votes \cup {<<a, b, v>>}
  /\ maxBal' = [maxBal EXCEPT ![a] = b]

Init ==
  /\ votes = {}
  /\ maxBal = [a \in Acceptor |-> -1]

Next ==
  \E a \in Acceptor, b \in Ballot:
    \/ AdvanceMaxBal(a, b)
    \/ \E v \in Value: Vote(a, b, v)

AllVotedFor(q, b, v) ==
  \A a \in q: <<a, b, v>> \in votes

chosen ==
  {v \in Value: (\E q \in Quorum, b \in Ballot: AllVotedFor(q, b, v))}

TypeOK ==
  /\ votes \subseteq Acceptor \X Ballot \X Value
  /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
  /\ \A v1, v2 \in chosen: v1 = v2
\*   /\ chosen = {}

====
