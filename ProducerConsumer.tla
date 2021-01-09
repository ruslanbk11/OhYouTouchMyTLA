-------------------------- MODULE ProducerConsumer --------------------------
EXTENDS Integers
(* --algorithm producerConsumer
variables queue = 0;

process producer = 0
variables temp;
begin
producerEnter: while TRUE do
    enterInconsistent: temp := queue;
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
            enterInconsistent1: temp := queue;
            takeOne: temp := temp - 1;
            returnConsistent1: queue := temp; 
        end if;
end while;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "31f62552" /\ chksum(tla) = "aa41f3f5")
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
                 /\ pc' = [pc EXCEPT ![0] = "enterInconsistent"]
                 /\ UNCHANGED << queue, temp_, temp >>

enterInconsistent == /\ pc[0] = "enterInconsistent"
                     /\ temp_' = queue
                     /\ pc' = [pc EXCEPT ![0] = "addNew"]
                     /\ UNCHANGED << queue, temp >>

addNew == /\ pc[0] = "addNew"
          /\ temp_' = queue + 1
          /\ pc' = [pc EXCEPT ![0] = "returnConsistent"]
          /\ UNCHANGED << queue, temp >>

returnConsistent == /\ pc[0] = "returnConsistent"
                    /\ queue' = temp_
                    /\ pc' = [pc EXCEPT ![0] = "producerEnter"]
                    /\ UNCHANGED << temp_, temp >>

producer == producerEnter \/ enterInconsistent \/ addNew
               \/ returnConsistent

consumerEnter == /\ pc[1] = "consumerEnter"
                 /\ pc' = [pc EXCEPT ![1] = "A"]
                 /\ UNCHANGED << queue, temp_, temp >>

A == /\ pc[1] = "A"
     /\ IF queue > 0
           THEN /\ pc' = [pc EXCEPT ![1] = "enterInconsistent1"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "consumerEnter"]
     /\ UNCHANGED << queue, temp_, temp >>

enterInconsistent1 == /\ pc[1] = "enterInconsistent1"
                      /\ temp' = queue
                      /\ pc' = [pc EXCEPT ![1] = "takeOne"]
                      /\ UNCHANGED << queue, temp_ >>

takeOne == /\ pc[1] = "takeOne"
           /\ temp' = temp - 1
           /\ pc' = [pc EXCEPT ![1] = "returnConsistent1"]
           /\ UNCHANGED << queue, temp_ >>

returnConsistent1 == /\ pc[1] = "returnConsistent1"
                     /\ queue' = temp
                     /\ pc' = [pc EXCEPT ![1] = "consumerEnter"]
                     /\ UNCHANGED << temp_, temp >>

consumer == consumerEnter \/ A \/ enterInconsistent1 \/ takeOne
               \/ returnConsistent1

Next == producer \/ consumer

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
NoBelowZeroQueue == queue >= 0
NoDoubleCriticalSection == pc[0] /= "addNew" /\ pc[1] /= "takeOne"
=============================================================================
\* Modification History
\* Last modified Sat Jan 09 16:36:49 MSK 2021 by ruslan
\* Created Sat Jan 09 16:15:09 MSK 2021 by ruslan
