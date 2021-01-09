-------------------------- MODULE ProducerConsumer --------------------------
EXTENDS Integers
(* --algorithm producerConsumer
variables queue = 0;

process producer = 0
variables temp;
begin
producerEnter: while TRUE do
    addNew: temp:= queue + 1;
    returnConsistent: queue := temp;
end while;
end process;

process consumer = 1
variables temp;
begin
consumerEnter: while TRUE do
    A:
        if queue > 0 then
            takeOne: temp := queue - 1;
            returnConsistent1: queue := temp; 
        end if;
end while;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "1a18e407" /\ chksum(tla) = "77865cb2")
\* Process variable temp of process producer at line 7 col 11 changed to temp_
CONSTANT defaultInitValue
VARIABLES queue, pc, temp_, temp

vars == << queue, pc, temp_, temp >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ queue = 0
        (* Process producer *)
        /\ temp_ = defaultInitValue
        (* Process consumer *)
        /\ temp = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "producerEnter"
                                        [] self = 1 -> "consumerEnter"]

producerEnter == /\ pc[0] = "producerEnter"
                 /\ pc' = [pc EXCEPT ![0] = "addNew"]
                 /\ UNCHANGED << queue, temp_, temp >>

addNew == /\ pc[0] = "addNew"
          /\ temp_' = queue + 1
          /\ pc' = [pc EXCEPT ![0] = "returnConsistent"]
          /\ UNCHANGED << queue, temp >>

returnConsistent == /\ pc[0] = "returnConsistent"
                    /\ queue' = temp_
                    /\ pc' = [pc EXCEPT ![0] = "producerEnter"]
                    /\ UNCHANGED << temp_, temp >>

producer == producerEnter \/ addNew \/ returnConsistent

consumerEnter == /\ pc[1] = "consumerEnter"
                 /\ pc' = [pc EXCEPT ![1] = "A"]
                 /\ UNCHANGED << queue, temp_, temp >>

A == /\ pc[1] = "A"
     /\ IF queue > 0
           THEN /\ pc' = [pc EXCEPT ![1] = "takeOne"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "consumerEnter"]
     /\ UNCHANGED << queue, temp_, temp >>

takeOne == /\ pc[1] = "takeOne"
           /\ temp' = queue - 1
           /\ pc' = [pc EXCEPT ![1] = "returnConsistent1"]
           /\ UNCHANGED << queue, temp_ >>

returnConsistent1 == /\ pc[1] = "returnConsistent1"
                     /\ queue' = temp
                     /\ pc' = [pc EXCEPT ![1] = "consumerEnter"]
                     /\ UNCHANGED << temp_, temp >>

consumer == consumerEnter \/ A \/ takeOne \/ returnConsistent1

Next == producer \/ consumer

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
NoBelowZeroQueue == queue >= 0
=============================================================================
\* Modification History
\* Last modified Sat Jan 09 16:27:22 MSK 2021 by ruslan
\* Created Sat Jan 09 16:15:09 MSK 2021 by ruslan
