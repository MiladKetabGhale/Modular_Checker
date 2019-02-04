open preamble AuxSpecTheory AuxIMPTheory
        
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

(* EWIN rule *)

val EWIN_Auxiliary_def = Define `
  EWIN_Auxiliary ((qu,st,l):params) j1 j2 =
    ∃u t p bl e h bl2.
      (j1 = NonFinal (u, t, p, bl, bl2, e, h))
      /\ (j2 = Final e) /\ ((LENGTH e = st) \/ (h = []))`;
 
(* HWIN rule *)

val HWIN_Auxiliary_def = Define `
  HWIN_Auxiliary ((qu,st,l):params) j1 j2 =
    ∃u t p bl e h bl2.
       (j1 = NonFinal (u, t, p, bl, bl2, e, h))
       /\ (j2 = Final (e++h))
       /\ ((LENGTH (e ++ h)) <= st)`;
 


(* Auxiliary ELIMINATION rule *)
  
val ELIM_CAND_Auxiliary_def = Define `
  ELIM_CAND_Auxiliary (c:cand) ((qu,st,l):params) ba (t: tallies) t' (p: piles) 
                      (np: piles) bl bl' (bl2: cand list) (e: cand list) e' 
                      (h: cand list) nh <=>
        (bl2 = [])
     /\ (ba = [])
     /\ (bl = [])
     /\ (bl' = [])
     /\ (t' = t)
     /\ (e' = e)
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
   
(* I am letting bl2 to have at most one cand in it at any time so no need to
 \/ ((~ (bl2 = [])) /\ (FLAT (get_cand_pile (HD bl2) p) = []))) *)
 
(*  /\ (bl2' = c :: bl2) :: to be added for Vic and Tasmania *)    

(* Auxiliary TRANSFER rule *)

val TRANSFER_Auxiliary_def = Define `
  TRANSFER_Auxiliary ((qu,st,l):params) (ba: ballots) (t: tallies) t'
                           (p: piles) (p': piles) (bl: cand list) (bl2: cand list) 
                           (bl2': cand list) e e' h h' <=>
        (bl2 = []) 
     /\ (bl <> [])
     /\ (ba = [])
     /\ (bl2' = [])
     /\ (t' = t)
     /\ (e' = e)
     /\ (h' = h)
     /\ (LENGTH e < st)
     /\ (!d. MEM d (h++e) ==> MEM d l)
     /\ (!d. MEM d bl ==> MEM d l)
     /\ ALL_DISTINCT (h++e)
     /\ (Valid_PileTally t l)
     /\ (Valid_PileTally p l)
     /\ (Valid_PileTally p' l)
     /\ (Valid_Init_CandList l)
     /\ ALL_DISTINCT (MAP FST t)
     /\ ALL_DISTINCT (MAP FST p)
     /\ (!c'. (MEM c' h ==> (?x. MEM (c',x) t /\ ( x < qu))))`;
 
(*
\/ ((bl2 <> []) /\ ((FLAT (get_cand_pile (HD bl2) p)) = [])))
*)

(* Auxiliary COUNT rule *)

val COUNT_Auxiliary_def = Define `
        (COUNT_Auxiliary ((qu, st, l): params) (ba: ballots) (ba': ballots) (t: tallies)
                         (t': tallies) (p: piles) (p': piles) (bl: cand list) bl' (e: cand list) e' (h: cand list) h') <=> 
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
       /\ (ba' = [])
       /\ (e' = e) /\ (h' = h) /\ (bl' = bl) `;
 
(* Auxiliary ELECT rule *)

val ELECT_Auxiliary_def = Define `
  ELECT_Auxiliary ((qu,st,l):params) (ba: ballots) (t: tallies) t'
                   (p: piles) (p': piles) bl bl' bl2 bl2' (e: cand list) e' (h: cand list) h' l1 <=>
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
    /\ (!c. MEM c h ==> MEM c l)
    /\ (t' = t) /\ (bl2' = bl2)`;
 

val TRANSFER_EXCLUDED_Auxiliary_def = Define `
    TRANSFER_EXCLUDED_Auxiliary (qu,st,l) j1 j2 <=>
      (? ba ba' t t' p p' bl bl' bl2 bl2' e e' h h' bs c.
          (j1 = NonFinal (ba,t,p,bl,bl2,e,h))
     /\ (ba = []) /\ (t = t') /\ (e = e') /\ (h = h') /\ (bl = bl')
     /\ (bl2 = c :: bs)
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
     /\ (? xs. xs = ReGroup_Piles (QSORT3 (\x y. (SND x) <= (SND y)) (FLAT (get_cand_pile c p)))
        /\ (~ (xs = [])) 
        /\ (ba' = LAST xs)
        /\ MEM (c, TAKE ((LENGTH xs) - 1) xs) p')
     /\ (j2 = NonFinal (ba',t',p',bl',bl2',e',h')))`;

 

(*                      
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
   




/\ (get_cand_pile c p' =
                       TAKE ((LENGTH (get_cand_pile c p)) - 1) (get_cand_pile c p))
     /\ ba' = LAST (ReGroup_Piles (FLAT (get_cand_pile c p)))`;
  
val Merge_def = Define `
       (Merge [] ys <=> ys)
    /\ (Merge xs [] <=> xs)
    /\ (Merge (x0 :: xs) (y0 :: ys) <=> if (SND x0) <= (SND y0) then x0 :: (Merge xs (y0::ys))
                                        else y0 :: (Merge  (x0:: xs) ys))`;


  
val MergeSort_def = tDefine "MergeSort" `
       (MergeSort [] <=> [])
    /\ (MergeSort [x] <=> [x])
    /\ (MergeSort xs <=> let half = DIV2 (LENGTH xs) in
                           Merge (MergeSort (TAKE half xs)) (MergeSort (DROP half xs)))`
WF_REL_TAC `measure (LENGTH)`                           
 *)  


val _ = export_theory ();
