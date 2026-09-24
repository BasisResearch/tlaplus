---- MODULE Guards ----
EXTENDS Naturals
VARIABLES x, pc

Init == x = 0 /\ pc = "a"

\* Each guard is false somewhere before any primed variable is assigned.
A == pc = "a" /\ x' = x + 1 /\ pc' = "b"
B == pc = "b" /\ x \in {1} /\ x' = x + 1 /\ pc' = "c"
C == x < 1 /\ x' = x /\ pc' = "c"

Next == A \/ B \/ C
====
