open preamble AuxSpecTheory
 
val _ = new_theory "AuxRulesSpec";

(* The rules *)

(* Each of rule corresponds to a step of vote counting
   A rule is of the following form:
   RULE (qu,st,l) j1 j2
   where
     (parameters of the election)
       qu is the quota (least amount of vote necessary to be elected)
       st is the number of seats
       l  is the list of initial candidates
     (transition step)
       j1 is the judgement before the rule application
       j2 is the judgement after the rule application
*)


(* Auxiliary ELIMINATION rule *)
  
val ELIM_CAND_Auxiliary_def = Define `
  ELIM_CAND_Auxiliary (c:cand) ((qu,st,l):params) (t: tallies) (p: piles) 
                      (np: piles) (bl2: cand list) bl2' (e: cand list) 
                      (h: cand list) nh <=>
   
        (((bl2 = []) \/ ((~ (bl2 = [])) /\ (FLAT (get_cand_pile (HD bl2) p) = [])))
(*     /\ (bl = []) /\ (bl' = [])
     /\ (ba = []) *)
     /\ Valid_Init_CandList l
     /\ (!c'. MEM c' (h++e) ==> (MEM c' l))
     /\ ALL_DISTINCT (h++e)
     /\ Valid_PileTally p l
     /\ Valid_PileTally np l
     /\ LENGTH (e ++ h) > st
     /\ LENGTH e < st
     /\ ALL_DISTINCT (MAP FST t)
     /\ Valid_PileTally t l
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))
     /\ MEM c h
     /\ (!d. (MEM d h ==> (?x y. (MEM (c,x) t) /\ (MEM (d,y) t) /\ ( x <= y))))
     /\ equal_except c nh h)`;
  
(*  /\ (bl2' = c :: bl2) :: to be added for Vic and Tasmania *)    

(* Auxiliary TRANSFER rule *)

val TRANSFER_Auxiliary_def = Define `
  TRANSFER_Auxiliary ((qu,st,l):params) (t: tallies)
                           (p: piles) (p': piles) (bl: cand list) (bl2: cand list) 
                           (e: cand list) (h: cand list) <=>
(*    ? nba t p bl e h nbl np.
     (j1 = NonFinal ([], t, p, bl, [], e, h)) *)
        ((bl2 = []) \/ ((bl2 <> []) /\ ((FLAT (get_cand_pile (HD bl2) p)) = [])))
(*     /\ (ba = []) *)
     /\ (bl <> [])
     /\ (LENGTH e < st)
     /\ (!d. MEM d (h++e) ==> MEM d l)
     /\ ALL_DISTINCT (h++e)
     /\ (Valid_PileTally t l)
     /\ (Valid_PileTally p l)
     /\ (Valid_PileTally p' l)
     /\ (Valid_Init_CandList l)
     /\ ALL_DISTINCT (MAP FST t)
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))`;
(*
           /\ (j2 = NonFinal (nba, t, np, nbl, [], e, h))`; *)

(* Auxiliary COUNT rule *)

val COUNT_Auxiliary_def = Define `
        (COUNT_Auxiliary ((qu, st, l): params) (ba: ballots) (ba': ballots) (t: tallies)
                         (t': tallies) (p: piles) (p': piles) (e: cand list) (h: cand list)) <=> 

(*? ba t nt p np bl bl2 e h.
          (j1 = NonFinal (ba, t, p, bl, bl2, e, h)) *)
          (!d. MEM d (h++e) ==> MEM d l)
       /\ ALL_DISTINCT (h++e)
       /\ (Valid_PileTally t l)
       /\ (Valid_PileTally t' l)
       /\ (Valid_PileTally p l)
       /\ (Valid_PileTally p' l)
       /\ (Valid_Init_CandList l)
       /\ ALL_DISTINCT (MAP FST p)
       /\ ALL_DISTINCT (MAP FST t)
       /\ ALL_DISTINCT (MAP FST p')
       /\ ALL_DISTINCT (MAP FST t')
       /\ (ba <> [])
       /\ (h <> [])
       /\ (ba' = []) `;
(*
       /\ (j2 = NonFinal ([], nt, np, bl, bl2, e, h)))`;
*)

(* Auxiliary ELECT rule *)

val ELECT_Auxiliary_def = Define `
  ELECT_Auxiliary ((qu,st,l):params) (ba: ballots) (t: tallies)
                   (p: piles) (p': piles) bl bl' (e: cand list) e' (h: cand list) h' <=>
 
(* (? t p bl e h nh ne np nbl l1 .
    (j1 = NonFinal ([], t, p, bl, [], e, h)) *)
    ? l1. 
       (l1 <> [])
    /\ (SORTED (tally_comparison t) l1)
    /\ (!c. MEM c l1 ==> (!(r :rat). MEM (c,r) t ==> (qu <= r)))
    /\ (LENGTH (l1 ++ e) <= st)
    /\ (!c. MEM c l1 \/ MEM c h' ==> MEM c h)
    /\ (!c. MEM c h ==> MEM c h' \/ MEM c l1)
    /\ (ba = [])
    /\ ALL_DISTINCT h
    /\ ALL_DISTINCT (l1 ++ h')
    /\ ALL_DISTINCT (l1 ++ e)
    /\ ALL_DISTINCT e'
    /\ (!c. MEM c l1 \/ MEM c e ==> MEM c e')
    /\ (!c. MEM c e' ==> MEM c e \/ MEM c l1)
    /\ (!c. MEM c h /\ (~ MEM c l1) ==> (!l'. MEM (c,l') p' <=> MEM (c,l') p))
    /\ ALL_DISTINCT (MAP FST p)
    /\ ALL_DISTINCT (MAP FST t)
    /\ ALL_DISTINCT (MAP FST p')
    /\ (0 < qu)
    /\ (bl' = bl ++ l1) 
    /\ (Valid_Init_CandList l)
    /\ (Valid_PileTally t l)
    /\ (Valid_PileTally p l)
    /\ (Valid_PileTally p' l)
    /\ (!c. MEM c e' ==> MEM c l)
    /\ (!c. MEM c h ==> MEM c l)`;
(*
    /\ (j2 = NonFinal ([], t, np, nbl, [], ne, nh)))`;
*)

val _ = export_theory ();
