---- MODULE GuardsConstraint ----
EXTENDS Naturals
VARIABLES x

Init == x = 0

A == x < 5 /\ x' = x + 1
B == x = 10 /\ x' = 0

Next == A \/ B

Small == x < 3
====
