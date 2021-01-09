------------------------- MODULE ConditionVariables -------------------------
EXTENDS Integers
(* --algorithm ConditionVariables
variables queue = 0, mutex = "";
process thread0 = 0
begin
thread0Enter: while TRUE do
    MonitorEnter0:
        await mutex = "";
        mutex := "thread0";
    A: if (queue = 0) then
            mutex := "";
            a1: await mutex = "Pulsed";
            a2: await mutex = "";
                mutex := "thread0";
        end if;
    deque0: queue := queue - 1;
            mutex := "";
end while;
end process;
process thread1 = 1
begin
thread1Enter: while TRUE do
    MonitorEnter1:
        await mutex = "";
        mutex := "thread1";
    A1: if (queue = 0) then
             mutex := "";
            a10: await mutex = "Pulsed";
            a12: await mutex = "";
                mutex := "thread1";
        end if;
    deque1: queue := queue - 1;
            mutex := "";
end while;
end process;
process thread2 = 2
begin
thread2Enter: while TRUE do
    MonitorEnter2:
        await mutex = "";
        mutex := "thread2";
    Enque: queue := queue + 1;
    MonitorPulseAll: mutex := "Pulsed";
    MonitorExit: mutex := "";
        
end while;
end process;
end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "e3b3704" /\ chksum(tla) = "80bee6a6")
VARIABLES queue, mutex, pc

vars == << queue, mutex, pc >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ queue = 0
        /\ mutex = ""
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "thread0Enter"
                                        [] self = 1 -> "thread1Enter"
                                        [] self = 2 -> "thread2Enter"]

thread0Enter == /\ pc[0] = "thread0Enter"
                /\ pc' = [pc EXCEPT ![0] = "MonitorEnter0"]
                /\ UNCHANGED << queue, mutex >>

MonitorEnter0 == /\ pc[0] = "MonitorEnter0"
                 /\ mutex = ""
                 /\ mutex' = "thread0"
                 /\ pc' = [pc EXCEPT ![0] = "A"]
                 /\ queue' = queue

A == /\ pc[0] = "A"
     /\ IF (queue = 0)
           THEN /\ mutex' = ""
                /\ pc' = [pc EXCEPT ![0] = "a1"]
           ELSE /\ pc' = [pc EXCEPT ![0] = "deque0"]
                /\ mutex' = mutex
     /\ queue' = queue

a1 == /\ pc[0] = "a1"
      /\ mutex = "Pulsed"
      /\ pc' = [pc EXCEPT ![0] = "a2"]
      /\ UNCHANGED << queue, mutex >>

a2 == /\ pc[0] = "a2"
      /\ mutex = ""
      /\ mutex' = "thread0"
      /\ pc' = [pc EXCEPT ![0] = "deque0"]
      /\ queue' = queue

deque0 == /\ pc[0] = "deque0"
          /\ queue' = queue - 1
          /\ mutex' = ""
          /\ pc' = [pc EXCEPT ![0] = "thread0Enter"]

thread0 == thread0Enter \/ MonitorEnter0 \/ A \/ a1 \/ a2 \/ deque0

thread1Enter == /\ pc[1] = "thread1Enter"
                /\ pc' = [pc EXCEPT ![1] = "MonitorEnter1"]
                /\ UNCHANGED << queue, mutex >>

MonitorEnter1 == /\ pc[1] = "MonitorEnter1"
                 /\ mutex = ""
                 /\ mutex' = "thread1"
                 /\ pc' = [pc EXCEPT ![1] = "A1"]
                 /\ queue' = queue

A1 == /\ pc[1] = "A1"
      /\ IF (queue = 0)
            THEN /\ mutex' = ""
                 /\ pc' = [pc EXCEPT ![1] = "a10"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "deque1"]
                 /\ mutex' = mutex
      /\ queue' = queue

a10 == /\ pc[1] = "a10"
       /\ mutex = "Pulsed"
       /\ pc' = [pc EXCEPT ![1] = "a12"]
       /\ UNCHANGED << queue, mutex >>

a12 == /\ pc[1] = "a12"
       /\ mutex = ""
       /\ mutex' = "thread1"
       /\ pc' = [pc EXCEPT ![1] = "deque1"]
       /\ queue' = queue

deque1 == /\ pc[1] = "deque1"
          /\ queue' = queue - 1
          /\ mutex' = ""
          /\ pc' = [pc EXCEPT ![1] = "thread1Enter"]

thread1 == thread1Enter \/ MonitorEnter1 \/ A1 \/ a10 \/ a12 \/ deque1

thread2Enter == /\ pc[2] = "thread2Enter"
                /\ pc' = [pc EXCEPT ![2] = "MonitorEnter2"]
                /\ UNCHANGED << queue, mutex >>

MonitorEnter2 == /\ pc[2] = "MonitorEnter2"
                 /\ mutex = ""
                 /\ mutex' = "thread2"
                 /\ pc' = [pc EXCEPT ![2] = "Enque"]
                 /\ queue' = queue

Enque == /\ pc[2] = "Enque"
         /\ queue' = queue + 1
         /\ pc' = [pc EXCEPT ![2] = "MonitorPulseAll"]
         /\ mutex' = mutex

MonitorPulseAll == /\ pc[2] = "MonitorPulseAll"
                   /\ mutex' = "Pulsed"
                   /\ pc' = [pc EXCEPT ![2] = "MonitorExit"]
                   /\ queue' = queue

MonitorExit == /\ pc[2] = "MonitorExit"
               /\ mutex' = ""
               /\ pc' = [pc EXCEPT ![2] = "thread2Enter"]
               /\ queue' = queue

thread2 == thread2Enter \/ MonitorEnter2 \/ Enque \/ MonitorPulseAll
              \/ MonitorExit

Next == thread0 \/ thread1 \/ thread2

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
NoBelowZeroQueue == queue >= 0
=============================================================================
\* Modification History
\* Last modified Sat Jan 09 17:13:00 MSK 2021 by ruslan
\* Created Sat Jan 09 16:48:34 MSK 2021 by ruslan
