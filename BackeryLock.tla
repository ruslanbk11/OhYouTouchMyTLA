---------------------------- MODULE BackeryLock ----------------------------
EXTENDS Integers, Sequences

CONSTANT N, MaxTokenNumber
(*
--algorithm criticalsection6bakery
{
    variables choosing = [x \in 1..N |-> FALSE]; number = [x \in 1..N |-> 0];
        lesslessret = [x \in 1..N |-> FALSE]; maxret = [x \in 1..N |-> 0];
    procedure NCS()
        variable isEndless;
    {
        ncs0: with (x \in {0,1}) {
                  isEndless := x;
              };
        ncs1: if (isEndless = 1) {
                  ncs2: while (TRUE) {
                      ncs3: skip;
                  }
              } else {
                  ncs4: return;
              }
    }
    procedure lessless(i, j) 
        variables numberi, numberj
    {
        ll1: numberi := number[i];
        ll2: numberj := number[j];
        ll3: if (numberi < numberj) {
                 \* number[i] < number[j]
                 lesslessret[i] := TRUE;
                 return;
             };
        ll4: if (numberi = numberj /\ i < j) {
             \* number[i] = number[j] and i < j
                 lesslessret[i] := TRUE;
                 return;
             };
        \* number[i] > number[j] or (number[i] = number[j] and i >= j)
        ll5: lesslessret[i] := FALSE; 
             return;
    }
    procedure max() 
        variables m = -1; k = 1; temp;
    {
        max1: while (k <= N) {
            max2: temp := number[k];
            max3: if (temp > m) {
                      m := temp;
                  };
                  k := k+1;     
        };
        max4: maxret[self] := m;
        max5: return;  
    }
    
   procedure wait(i_, j_) 
       variables numberi_; numberj_;
   {
       wait1: while (TRUE) {
                  wait2: numberi_ := number[i_];
                  wait3: numberj_ := number[j_];
                  wait4: call lessless(i_,j_);
                  wait5: if (numberj_ = 0 \/ lesslessret[i_] = TRUE) {
                             wait6: return;
                         };
              };
   }
   
    process(Proc \in 1..N) 
        variables i = self; j; otherprocesses;
    {
        p0: while (TRUE) {
                p1: call NCS(); \* non-critical section
                p2: choosing[i] := TRUE;
                \* Note that max() is non-atomic! 
                p3a: call max();
                p3b: if (maxret[self] >= MaxTokenNumber) {
                    \* After next line: number[i] = MaxTokenNumber
                    maxret[self] := MaxTokenNumber-1;
                };
                p3c: number[i] := 1 + maxret[self];
                p4: choosing[self] := FALSE;
                p5a: otherprocesses := 1..N \ {i};
                p5b: while (otherprocesses # {}) {
                         with (proc \in otherprocesses) {
                             j := proc;
                         };
                         otherprocesses := otherprocesses \ {j};
                         p6: await choosing[j] = FALSE;
                         p7: call wait(i,j);
                     };
                p8: skip;
                p9: number[i] := 0; 
            };
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "3697e4ee" /\ chksum(tla) = "787bde38")
\* Process variable i of process Proc at line 71 col 19 changed to i_P
\* Process variable j of process Proc at line 71 col 29 changed to j_P
CONSTANT defaultInitValue
VARIABLES choosing, number, lesslessret, maxret, pc, stack, isEndless, i, j, 
          numberi, numberj, m, k, temp, i_, j_, numberi_, numberj_, i_P, j_P, 
          otherprocesses

vars == << choosing, number, lesslessret, maxret, pc, stack, isEndless, i, j, 
           numberi, numberj, m, k, temp, i_, j_, numberi_, numberj_, i_P, j_P, 
           otherprocesses >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ choosing = [x \in 1..N |-> FALSE]
        /\ number = [x \in 1..N |-> 0]
        /\ lesslessret = [x \in 1..N |-> FALSE]
        /\ maxret = [x \in 1..N |-> 0]
        (* Procedure NCS *)
        /\ isEndless = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure lessless *)
        /\ i = [ self \in ProcSet |-> defaultInitValue]
        /\ j = [ self \in ProcSet |-> defaultInitValue]
        /\ numberi = [ self \in ProcSet |-> defaultInitValue]
        /\ numberj = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure max *)
        /\ m = [ self \in ProcSet |-> -1]
        /\ k = [ self \in ProcSet |-> 1]
        /\ temp = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wait *)
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        /\ j_ = [ self \in ProcSet |-> defaultInitValue]
        /\ numberi_ = [ self \in ProcSet |-> defaultInitValue]
        /\ numberj_ = [ self \in ProcSet |-> defaultInitValue]
        (* Process Proc *)
        /\ i_P = [self \in 1..N |-> self]
        /\ j_P = [self \in 1..N |-> defaultInitValue]
        /\ otherprocesses = [self \in 1..N |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "p0"]

ncs0(self) == /\ pc[self] = "ncs0"
              /\ \E x \in {0,1}:
                   isEndless' = [isEndless EXCEPT ![self] = x]
              /\ pc' = [pc EXCEPT ![self] = "ncs1"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, i, 
                              j, numberi, numberj, m, k, temp, i_, j_, 
                              numberi_, numberj_, i_P, j_P, otherprocesses >>

ncs1(self) == /\ pc[self] = "ncs1"
              /\ IF isEndless[self] = 1
                    THEN /\ pc' = [pc EXCEPT ![self] = "ncs2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ncs4"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i, j, numberi, numberj, m, k, temp, 
                              i_, j_, numberi_, numberj_, i_P, j_P, 
                              otherprocesses >>

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "ncs3"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i, j, numberi, numberj, m, k, temp, 
                              i_, j_, numberi_, numberj_, i_P, j_P, 
                              otherprocesses >>

ncs3(self) == /\ pc[self] = "ncs3"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i, j, numberi, numberj, m, k, temp, 
                              i_, j_, numberi_, numberj_, i_P, j_P, 
                              otherprocesses >>

ncs4(self) == /\ pc[self] = "ncs4"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ isEndless' = [isEndless EXCEPT ![self] = Head(stack[self]).isEndless]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, i, j, 
                              numberi, numberj, m, k, temp, i_, j_, numberi_, 
                              numberj_, i_P, j_P, otherprocesses >>

NCS(self) == ncs0(self) \/ ncs1(self) \/ ncs2(self) \/ ncs3(self)
                \/ ncs4(self)

ll1(self) == /\ pc[self] = "ll1"
             /\ numberi' = [numberi EXCEPT ![self] = number[i[self]]]
             /\ pc' = [pc EXCEPT ![self] = "ll2"]
             /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                             isEndless, i, j, numberj, m, k, temp, i_, j_, 
                             numberi_, numberj_, i_P, j_P, otherprocesses >>

ll2(self) == /\ pc[self] = "ll2"
             /\ numberj' = [numberj EXCEPT ![self] = number[j[self]]]
             /\ pc' = [pc EXCEPT ![self] = "ll3"]
             /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                             isEndless, i, j, numberi, m, k, temp, i_, j_, 
                             numberi_, numberj_, i_P, j_P, otherprocesses >>

ll3(self) == /\ pc[self] = "ll3"
             /\ IF numberi[self] < numberj[self]
                   THEN /\ lesslessret' = [lesslessret EXCEPT ![i[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ numberi' = [numberi EXCEPT ![self] = Head(stack[self]).numberi]
                        /\ numberj' = [numberj EXCEPT ![self] = Head(stack[self]).numberj]
                        /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                        /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ll4"]
                        /\ UNCHANGED << lesslessret, stack, i, j, numberi, 
                                        numberj >>
             /\ UNCHANGED << choosing, number, maxret, isEndless, m, k, temp, 
                             i_, j_, numberi_, numberj_, i_P, j_P, 
                             otherprocesses >>

ll4(self) == /\ pc[self] = "ll4"
             /\ IF numberi[self] = numberj[self] /\ i[self] < j[self]
                   THEN /\ lesslessret' = [lesslessret EXCEPT ![i[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ numberi' = [numberi EXCEPT ![self] = Head(stack[self]).numberi]
                        /\ numberj' = [numberj EXCEPT ![self] = Head(stack[self]).numberj]
                        /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
                        /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ll5"]
                        /\ UNCHANGED << lesslessret, stack, i, j, numberi, 
                                        numberj >>
             /\ UNCHANGED << choosing, number, maxret, isEndless, m, k, temp, 
                             i_, j_, numberi_, numberj_, i_P, j_P, 
                             otherprocesses >>

ll5(self) == /\ pc[self] = "ll5"
             /\ lesslessret' = [lesslessret EXCEPT ![i[self]] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ numberi' = [numberi EXCEPT ![self] = Head(stack[self]).numberi]
             /\ numberj' = [numberj EXCEPT ![self] = Head(stack[self]).numberj]
             /\ i' = [i EXCEPT ![self] = Head(stack[self]).i]
             /\ j' = [j EXCEPT ![self] = Head(stack[self]).j]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << choosing, number, maxret, isEndless, m, k, temp, 
                             i_, j_, numberi_, numberj_, i_P, j_P, 
                             otherprocesses >>

lessless(self) == ll1(self) \/ ll2(self) \/ ll3(self) \/ ll4(self)
                     \/ ll5(self)

max1(self) == /\ pc[self] = "max1"
              /\ IF k[self] <= N
                    THEN /\ pc' = [pc EXCEPT ![self] = "max2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "max4"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i, j, numberi, numberj, m, k, temp, 
                              i_, j_, numberi_, numberj_, i_P, j_P, 
                              otherprocesses >>

max2(self) == /\ pc[self] = "max2"
              /\ temp' = [temp EXCEPT ![self] = number[k[self]]]
              /\ pc' = [pc EXCEPT ![self] = "max3"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i, j, numberi, numberj, m, k, i_, j_, 
                              numberi_, numberj_, i_P, j_P, otherprocesses >>

max3(self) == /\ pc[self] = "max3"
              /\ IF temp[self] > m[self]
                    THEN /\ m' = [m EXCEPT ![self] = temp[self]]
                    ELSE /\ TRUE
                         /\ m' = m
              /\ k' = [k EXCEPT ![self] = k[self]+1]
              /\ pc' = [pc EXCEPT ![self] = "max1"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i, j, numberi, numberj, temp, i_, j_, 
                              numberi_, numberj_, i_P, j_P, otherprocesses >>

max4(self) == /\ pc[self] = "max4"
              /\ maxret' = [maxret EXCEPT ![self] = m[self]]
              /\ pc' = [pc EXCEPT ![self] = "max5"]
              /\ UNCHANGED << choosing, number, lesslessret, stack, isEndless, 
                              i, j, numberi, numberj, m, k, temp, i_, j_, 
                              numberi_, numberj_, i_P, j_P, otherprocesses >>

max5(self) == /\ pc[self] = "max5"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ m' = [m EXCEPT ![self] = Head(stack[self]).m]
              /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
              /\ temp' = [temp EXCEPT ![self] = Head(stack[self]).temp]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, isEndless, 
                              i, j, numberi, numberj, i_, j_, numberi_, 
                              numberj_, i_P, j_P, otherprocesses >>

max(self) == max1(self) \/ max2(self) \/ max3(self) \/ max4(self)
                \/ max5(self)

wait1(self) == /\ pc[self] = "wait1"
               /\ pc' = [pc EXCEPT ![self] = "wait2"]
               /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                               isEndless, i, j, numberi, numberj, m, k, temp, 
                               i_, j_, numberi_, numberj_, i_P, j_P, 
                               otherprocesses >>

wait2(self) == /\ pc[self] = "wait2"
               /\ numberi_' = [numberi_ EXCEPT ![self] = number[i_[self]]]
               /\ pc' = [pc EXCEPT ![self] = "wait3"]
               /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                               isEndless, i, j, numberi, numberj, m, k, temp, 
                               i_, j_, numberj_, i_P, j_P, otherprocesses >>

wait3(self) == /\ pc[self] = "wait3"
               /\ numberj_' = [numberj_ EXCEPT ![self] = number[j_[self]]]
               /\ pc' = [pc EXCEPT ![self] = "wait4"]
               /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                               isEndless, i, j, numberi, numberj, m, k, temp, 
                               i_, j_, numberi_, i_P, j_P, otherprocesses >>

wait4(self) == /\ pc[self] = "wait4"
               /\ /\ i' = [i EXCEPT ![self] = i_[self]]
                  /\ j' = [j EXCEPT ![self] = j_[self]]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lessless",
                                                           pc        |->  "wait5",
                                                           numberi   |->  numberi[self],
                                                           numberj   |->  numberj[self],
                                                           i         |->  i[self],
                                                           j         |->  j[self] ] >>
                                                       \o stack[self]]
               /\ numberi' = [numberi EXCEPT ![self] = defaultInitValue]
               /\ numberj' = [numberj EXCEPT ![self] = defaultInitValue]
               /\ pc' = [pc EXCEPT ![self] = "ll1"]
               /\ UNCHANGED << choosing, number, lesslessret, maxret, 
                               isEndless, m, k, temp, i_, j_, numberi_, 
                               numberj_, i_P, j_P, otherprocesses >>

wait5(self) == /\ pc[self] = "wait5"
               /\ IF numberj_[self] = 0 \/ lesslessret[i_[self]] = TRUE
                     THEN /\ pc' = [pc EXCEPT ![self] = "wait6"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "wait1"]
               /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                               isEndless, i, j, numberi, numberj, m, k, temp, 
                               i_, j_, numberi_, numberj_, i_P, j_P, 
                               otherprocesses >>

wait6(self) == /\ pc[self] = "wait6"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ numberi_' = [numberi_ EXCEPT ![self] = Head(stack[self]).numberi_]
               /\ numberj_' = [numberj_ EXCEPT ![self] = Head(stack[self]).numberj_]
               /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
               /\ j_' = [j_ EXCEPT ![self] = Head(stack[self]).j_]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << choosing, number, lesslessret, maxret, 
                               isEndless, i, j, numberi, numberj, m, k, temp, 
                               i_P, j_P, otherprocesses >>

wait(self) == wait1(self) \/ wait2(self) \/ wait3(self) \/ wait4(self)
                 \/ wait5(self) \/ wait6(self)

p0(self) == /\ pc[self] = "p0"
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                            isEndless, i, j, numberi, numberj, m, k, temp, i_, 
                            j_, numberi_, numberj_, i_P, j_P, otherprocesses >>

p1(self) == /\ pc[self] = "p1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "NCS",
                                                     pc        |->  "p2",
                                                     isEndless |->  isEndless[self] ] >>
                                                 \o stack[self]]
            /\ isEndless' = [isEndless EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ncs0"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, i, j, 
                            numberi, numberj, m, k, temp, i_, j_, numberi_, 
                            numberj_, i_P, j_P, otherprocesses >>

p2(self) == /\ pc[self] = "p2"
            /\ choosing' = [choosing EXCEPT ![i_P[self]] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p3a"]
            /\ UNCHANGED << number, lesslessret, maxret, stack, isEndless, i, 
                            j, numberi, numberj, m, k, temp, i_, j_, numberi_, 
                            numberj_, i_P, j_P, otherprocesses >>

p3a(self) == /\ pc[self] = "p3a"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "max",
                                                      pc        |->  "p3b",
                                                      m         |->  m[self],
                                                      k         |->  k[self],
                                                      temp      |->  temp[self] ] >>
                                                  \o stack[self]]
             /\ m' = [m EXCEPT ![self] = -1]
             /\ k' = [k EXCEPT ![self] = 1]
             /\ temp' = [temp EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "max1"]
             /\ UNCHANGED << choosing, number, lesslessret, maxret, isEndless, 
                             i, j, numberi, numberj, i_, j_, numberi_, 
                             numberj_, i_P, j_P, otherprocesses >>

p3b(self) == /\ pc[self] = "p3b"
             /\ IF maxret[self] >= MaxTokenNumber
                   THEN /\ maxret' = [maxret EXCEPT ![self] = MaxTokenNumber-1]
                   ELSE /\ TRUE
                        /\ UNCHANGED maxret
             /\ pc' = [pc EXCEPT ![self] = "p3c"]
             /\ UNCHANGED << choosing, number, lesslessret, stack, isEndless, 
                             i, j, numberi, numberj, m, k, temp, i_, j_, 
                             numberi_, numberj_, i_P, j_P, otherprocesses >>

p3c(self) == /\ pc[self] = "p3c"
             /\ number' = [number EXCEPT ![i_P[self]] = 1 + maxret[self]]
             /\ pc' = [pc EXCEPT ![self] = "p4"]
             /\ UNCHANGED << choosing, lesslessret, maxret, stack, isEndless, 
                             i, j, numberi, numberj, m, k, temp, i_, j_, 
                             numberi_, numberj_, i_P, j_P, otherprocesses >>

p4(self) == /\ pc[self] = "p4"
            /\ choosing' = [choosing EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "p5a"]
            /\ UNCHANGED << number, lesslessret, maxret, stack, isEndless, i, 
                            j, numberi, numberj, m, k, temp, i_, j_, numberi_, 
                            numberj_, i_P, j_P, otherprocesses >>

p5a(self) == /\ pc[self] = "p5a"
             /\ otherprocesses' = [otherprocesses EXCEPT ![self] = 1..N \ {i_P[self]}]
             /\ pc' = [pc EXCEPT ![self] = "p5b"]
             /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                             isEndless, i, j, numberi, numberj, m, k, temp, i_, 
                             j_, numberi_, numberj_, i_P, j_P >>

p5b(self) == /\ pc[self] = "p5b"
             /\ IF otherprocesses[self] # {}
                   THEN /\ \E proc \in otherprocesses[self]:
                             j_P' = [j_P EXCEPT ![self] = proc]
                        /\ otherprocesses' = [otherprocesses EXCEPT ![self] = otherprocesses[self] \ {j_P'[self]}]
                        /\ pc' = [pc EXCEPT ![self] = "p6"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "p8"]
                        /\ UNCHANGED << j_P, otherprocesses >>
             /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                             isEndless, i, j, numberi, numberj, m, k, temp, i_, 
                             j_, numberi_, numberj_, i_P >>

p6(self) == /\ pc[self] = "p6"
            /\ choosing[j_P[self]] = FALSE
            /\ pc' = [pc EXCEPT ![self] = "p7"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                            isEndless, i, j, numberi, numberj, m, k, temp, i_, 
                            j_, numberi_, numberj_, i_P, j_P, otherprocesses >>

p7(self) == /\ pc[self] = "p7"
            /\ /\ i_' = [i_ EXCEPT ![self] = i_P[self]]
               /\ j_' = [j_ EXCEPT ![self] = j_P[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wait",
                                                        pc        |->  "p5b",
                                                        numberi_  |->  numberi_[self],
                                                        numberj_  |->  numberj_[self],
                                                        i_        |->  i_[self],
                                                        j_        |->  j_[self] ] >>
                                                    \o stack[self]]
            /\ numberi_' = [numberi_ EXCEPT ![self] = defaultInitValue]
            /\ numberj_' = [numberj_ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "wait1"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, isEndless, 
                            i, j, numberi, numberj, m, k, temp, i_P, j_P, 
                            otherprocesses >>

p8(self) == /\ pc[self] = "p8"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p9"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                            isEndless, i, j, numberi, numberj, m, k, temp, i_, 
                            j_, numberi_, numberj_, i_P, j_P, otherprocesses >>

p9(self) == /\ pc[self] = "p9"
            /\ number' = [number EXCEPT ![i_P[self]] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << choosing, lesslessret, maxret, stack, isEndless, i, 
                            j, numberi, numberj, m, k, temp, i_, j_, numberi_, 
                            numberj_, i_P, j_P, otherprocesses >>

Proc(self) == p0(self) \/ p1(self) \/ p2(self) \/ p3a(self) \/ p3b(self)
                 \/ p3c(self) \/ p4(self) \/ p5a(self) \/ p5b(self)
                 \/ p6(self) \/ p7(self) \/ p8(self) \/ p9(self)

Next == (\E self \in ProcSet:  \/ NCS(self) \/ lessless(self) \/ max(self)
                               \/ wait(self))
           \/ (\E self \in 1..N: Proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 
MutualExclusion == \A proc1, proc2 \in 1..N : (proc1 # proc2) => ~ (pc[proc1] = "p8" /\ pc[proc2] = "p8")
=============================================================================
\* Modification History
\* Last modified Fri Jan 08 23:21:49 MSK 2021 by ruslan
\* Created Fri Jan 08 22:55:09 MSK 2021 by ruslan
