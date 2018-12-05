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
   
        (bl2 = [])
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
     /\ equal_except c nh h`;
  

(* Auxiliary TRANSFER rule *)

val TRANSFER_Auxiliary_def = Define `
  TRANSFER_Auxiliary ((qu,st,l):params) (t: tallies)
                           (p: piles) (p': piles) (bl: cand list) (bl2: cand list) 
                           (e: cand list) (h: cand list) <=>
        (bl2 = [])
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

(* Auxiliary COUNT rule *)

val COUNT_Auxiliary_def = Define `
        (COUNT_Auxiliary ((qu, st, l): params) (ba: ballots) (ba': ballots) (t: tallies)
                         (t': tallies) (p: piles) (p': piles) (e: cand list) (h: cand list)) <=> 

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

(* Auxiliary ELECT rule *)

val ELECT_Auxiliary_def = Define `
  ELECT_Auxiliary ((qu,st,l):params) (ba: ballots) (t: tallies)
                   (p: piles) (p': piles) bl bl' (e: cand list) e' (h: cand list) h' <=>
 
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



val TRANSFER_EXCLUDED_Auxiliary_def = Define `
       TRANSFER_EXCLUDED_Auxiliary ((qu,st,l):params) ba' (t: tallies)
                           (p: piles) (p': piles) (bl2: cand list) bl2'
                           (e: cand list) (h: cand list) <=>
      ? bs c.
        (bl2 = c :: bs)
     /\ ((MEM (c, []) p' ==> (bl2' = []))
        /\ (~ MEM (c, []) p' ==> (bl2' = bl2)))
     /\ (LENGTH e < st)
     /\ (!d. MEM d (h++e) ==> MEM d l)
     /\ ALL_DISTINCT (h++e)
     /\ (Valid_PileTally t l)
     /\ (Valid_PileTally p l)
     /\ ALL_DISTINCT (MAP FST p')
     /\ (Valid_PileTally p' l)
     /\ (Valid_Init_CandList l)
     /\ ALL_DISTINCT (MAP FST t)
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))
     /\ (!d'. ~ MEM d' [c] ==>
        (!l'. (MEM (d',l') p ==> MEM (d',l') p')) /\ (!l'. (MEM (d',l') p' ==> MEM (d',l') p)))
     /\ ? xs. xs = ReGroup_Piles (QSORT3 (\x y. (SND x) <= (SND y)) (FLAT (get_cand_pile c p)))
        /\ (ba' = LAST xs)
        /\ MEM (c, TAKE ((LENGTH xs) - 1) xs) p' `;


val _ = export_theory ();
