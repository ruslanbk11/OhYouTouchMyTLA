-------------------------- MODULE ProducerConsumer --------------------------
EXTENDS Integers
(* --algorithm producerConsumer
variables queue = 0;

process producer = 0
begin
producerEnter: while TRUE do
    addNew: queue:= queue + 1;
end while;
end process;

process consumer = 1
variables temp;
begin
consumerEnter: while TRUE do
    A:
        if queue > 0 then
            takeOne: queue := queue - 1;
        end if;
end while;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "700f2089" /\ chksum(tla) = "75ad27e3")
CONSTANT defaultInitValue
VARIABLES queue, pc, temp

vars == << queue, pc, temp >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ queue = 0
        (* Process consumer *)
        /\ temp = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "producerEnter"
                                        [] self = 1 -> "consumerEnter"]

producerEnter == /\ pc[0] = "producerEnter"
                 /\ pc' = [pc EXCEPT ![0] = "addNew"]
                 /\ UNCHANGED << queue, temp >>

addNew == /\ pc[0] = "addNew"
          /\ queue' = queue + 1
          /\ pc' = [pc EXCEPT ![0] = "producerEnter"]
          /\ temp' = temp

producer == producerEnter \/ addNew

consumerEnter == /\ pc[1] = "consumerEnter"
                 /\ pc' = [pc EXCEPT ![1] = "A"]
                 /\ UNCHANGED << queue, temp >>

A == /\ pc[1] = "A"
     /\ IF queue > 0
           THEN /\ pc' = [pc EXCEPT ![1] = "takeOne"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "consumerEnter"]
     /\ UNCHANGED << queue, temp >>

takeOne == /\ pc[1] = "takeOne"
           /\ queue' = queue - 1
           /\ pc' = [pc EXCEPT ![1] = "consumerEnter"]
           /\ temp' = temp

consumer == consumerEnter \/ A \/ takeOne

Next == producer \/ consumer

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
NoBelowZeroQueue == queue >= 0
=============================================================================
\* Modification History
\* Last modified Sat Jan 09 16:31:33 MSK 2021 by ruslan
\* Created Sat Jan 09 16:15:09 MSK 2021 by ruslan
