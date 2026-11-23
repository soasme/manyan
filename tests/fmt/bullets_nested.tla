---- MODULE bullets_nested ----
EXTENDS Naturals
VARIABLE x, y, z

Nested ==
    \/ /\ x = 0
       /\ y = 0
       /\ \/ x' = 1
          \/ y' = 1
    \/ /\ x = 1
       /\ UNCHANGED <<x, y>>

SingleBullet ==
    /\ x = 0

LongInlineBreaks ==
    x = 1 /\ y = 2 /\ z = 3 /\ x + y = 3 /\ y + z = 5 /\ x + z = 4 /\ x + y + z = 6

LeftImpliesBreaks ==
    (x = 1 /\ y = 2 /\ z = 3 /\ x + y = 3 /\ y + z = 5 /\ x + z = 4) => x + y + z = 6

RightImpliesAndLeadsTo ==
    /\ x = 0 =>
        /\ y = 1
        /\ z = 2
    /\ x = 1 ~>
        \/ y = 0
        \/ z = 0

BulletInControl ==
    IF x = 0
    THEN /\ y = 1
         /\ z = 2
    ELSE LET a == x + 1
         IN  /\ y = a
             /\ z = a + 1
====
