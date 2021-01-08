----------------------------- MODULE DragonFire -----------------------------
EXTENDS Integers
(* --algorithm dragonFire
variables fireball = 0, firebrathing = "", c = 0;
process thread0 = 0
variables temp;
begin
thread0Enter: while TRUE do
    MonitorEnter:
        await firebrathing = "";
        firebrathing := "sorcerer";
    incinerate_enemies: skip;
    if1: if (fireball > 0) then
        fireball := fireball - 1;
        blast_enemies: skip;
        if2: if (fireball > 0) then
            fireball := fireball - 1;
            if3: if (fireball > 0) then
                fireball := fireball - 1;
                critical_section: skip;
                end if;
                end if;
                end if;
    c1: temp := c - 1;
    c12:    c := temp;
    c2: temp := c + 1;
    c22:    c := temp;
    MonitorExit:
        firebrathing := ""
end while;
end process;

process thread1 = 1
begin
thread1Enter: while TRUE do
    A:
        if c < 2 then
            release:
                fireball := fireball + 1;
        else 
            critical_section: skip;
        end if;
end while;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "d1b40c0a" /\ chksum(tla) = "2bdaeb0a")
\* Label critical_section of process thread0 at line 20 col 35 changed to critical_section_
CONSTANT defaultInitValue
VARIABLES fireball, firebrathing, c, pc, temp

vars == << fireball, firebrathing, c, pc, temp >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ fireball = 0
        /\ firebrathing = ""
        /\ c = 0
        (* Process thread0 *)
        /\ temp = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "thread0Enter"
                                        [] self = 1 -> "thread1Enter"]

thread0Enter == /\ pc[0] = "thread0Enter"
                /\ pc' = [pc EXCEPT ![0] = "MonitorEnter"]
                /\ UNCHANGED << fireball, firebrathing, c, temp >>

MonitorEnter == /\ pc[0] = "MonitorEnter"
                /\ firebrathing = ""
                /\ firebrathing' = "sorcerer"
                /\ pc' = [pc EXCEPT ![0] = "incinerate_enemies"]
                /\ UNCHANGED << fireball, c, temp >>

incinerate_enemies == /\ pc[0] = "incinerate_enemies"
                      /\ TRUE
                      /\ pc' = [pc EXCEPT ![0] = "if1"]
                      /\ UNCHANGED << fireball, firebrathing, c, temp >>

if1 == /\ pc[0] = "if1"
       /\ IF (fireball > 0)
             THEN /\ fireball' = fireball - 1
                  /\ pc' = [pc EXCEPT ![0] = "blast_enemies"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "c1"]
                  /\ UNCHANGED fireball
       /\ UNCHANGED << firebrathing, c, temp >>

blast_enemies == /\ pc[0] = "blast_enemies"
                 /\ TRUE
                 /\ pc' = [pc EXCEPT ![0] = "if2"]
                 /\ UNCHANGED << fireball, firebrathing, c, temp >>

if2 == /\ pc[0] = "if2"
       /\ IF (fireball > 0)
             THEN /\ fireball' = fireball - 1
                  /\ pc' = [pc EXCEPT ![0] = "if3"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "c1"]
                  /\ UNCHANGED fireball
       /\ UNCHANGED << firebrathing, c, temp >>

if3 == /\ pc[0] = "if3"
       /\ IF (fireball > 0)
             THEN /\ fireball' = fireball - 1
                  /\ pc' = [pc EXCEPT ![0] = "critical_section_"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "c1"]
                  /\ UNCHANGED fireball
       /\ UNCHANGED << firebrathing, c, temp >>

critical_section_ == /\ pc[0] = "critical_section_"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![0] = "c1"]
                     /\ UNCHANGED << fireball, firebrathing, c, temp >>

c1 == /\ pc[0] = "c1"
      /\ temp' = c - 1
      /\ pc' = [pc EXCEPT ![0] = "c12"]
      /\ UNCHANGED << fireball, firebrathing, c >>

c12 == /\ pc[0] = "c12"
       /\ c' = temp
       /\ pc' = [pc EXCEPT ![0] = "c2"]
       /\ UNCHANGED << fireball, firebrathing, temp >>

c2 == /\ pc[0] = "c2"
      /\ temp' = c + 1
      /\ pc' = [pc EXCEPT ![0] = "c22"]
      /\ UNCHANGED << fireball, firebrathing, c >>

c22 == /\ pc[0] = "c22"
       /\ c' = temp
       /\ pc' = [pc EXCEPT ![0] = "MonitorExit"]
       /\ UNCHANGED << fireball, firebrathing, temp >>

MonitorExit == /\ pc[0] = "MonitorExit"
               /\ firebrathing' = ""
               /\ pc' = [pc EXCEPT ![0] = "thread0Enter"]
               /\ UNCHANGED << fireball, c, temp >>

thread0 == thread0Enter \/ MonitorEnter \/ incinerate_enemies \/ if1
              \/ blast_enemies \/ if2 \/ if3 \/ critical_section_ \/ c1
              \/ c12 \/ c2 \/ c22 \/ MonitorExit

thread1Enter == /\ pc[1] = "thread1Enter"
                /\ pc' = [pc EXCEPT ![1] = "A"]
                /\ UNCHANGED << fireball, firebrathing, c, temp >>

A == /\ pc[1] = "A"
     /\ IF c < 2
           THEN /\ pc' = [pc EXCEPT ![1] = "release"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "critical_section"]
     /\ UNCHANGED << fireball, firebrathing, c, temp >>

release == /\ pc[1] = "release"
           /\ fireball' = fireball + 1
           /\ pc' = [pc EXCEPT ![1] = "thread1Enter"]
           /\ UNCHANGED << firebrathing, c, temp >>

critical_section == /\ pc[1] = "critical_section"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![1] = "thread1Enter"]
                    /\ UNCHANGED << fireball, firebrathing, c, temp >>

thread1 == thread1Enter \/ A \/ release \/ critical_section

Next == thread0 \/ thread1

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
NotDoubleCriticalSection == pc[0] /= "critical_section_" /\ pc[1] /= "critical_section"
=============================================================================
\* Modification History
\* Last modified Fri Jan 08 22:23:59 MSK 2021 by ruslan
\* Created Fri Jan 08 22:09:43 MSK 2021 by ruslan
