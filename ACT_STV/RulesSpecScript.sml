open preamble 
     AuxSpecTheory 
     AuxRulesSpecTheory
     AuxRulesIMPTheory
     AuxRulesEquivProofsTheory
     
val _ = new_theory "RulesSpec";

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

val EWIN_def = Define `
  EWIN ((qu,st,l):params) j1 j2 <=> EWIN_Auxiliary (qu,st,l) j1 j2`;
    
(* HWIN rule *)

val HWIN_def = Define `
  HWIN ((qu,st,l):params) j1 j2 <=> HWIN_Auxiliary (qu,st,l) j1 j2`;
 
(* ELIMINATION rule *)
    
val ELIM_CAND_def = Define `
  ELIM_CAND (c:cand) ((qu,st,l):params) j1 j2 <=>
    ?ba nba t nt p np bl nbl bl2 nbl2 e ne h nh.
     (j1 = NonFinal (ba, t, p, bl, bl2, e, h))
        /\ (ELIM_CAND_Auxiliary c (qu,st,l) ba t nt p np bl nbl bl2 e ne h nh)
        /\ (nbl2 = [])
        /\ (nba = FLAT (get_cand_pile c p))
        /\ MEM (c,[]) np
        /\ (!d'. ((d' <> c) ==>
           (!l. (MEM (d',l) p ==> MEM (d',l) np) /\ (MEM (d',l) np ==> MEM (d',l) p)))) /\
    (j2 = NonFinal (nba, nt, np, nbl, nbl2, ne, nh))`;
       
    
(* TRANSFER rule *)
 
val TRANSFER_def = Define `
  TRANSFER ((qu,st,l):params) j1 j2 =
    ? ba nba t nt p np bl nbl bl2 nbl2 e ne h nh.
     (j1 = NonFinal (ba, t, p, bl, bl2, e, h))
     /\ (TRANSFER_Auxiliary (qu,st,l) ba t nt p np bl bl2 nbl2 e ne h nh)
     /\ ? l' c.
              ((bl = c::l')
           /\ (MEM c l)
           /\ (!l''. MEM (c,l'') p ==> l'' <> [])
           /\ (nbl = l')
           /\ (nba = LAST (get_cand_pile c p))
           /\ (MEM (c,[]) np)
           /\ (!d'. ((d' <> c) ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np)
                            /\ (MEM (d',l') np ==> MEM (d',l') p)))))
           /\ (j2 = NonFinal (nba, nt, np, nbl, nbl2, ne, nh))`;


(* COUNT rule *)
 
val COUNT_def = Define `
         (COUNT (qu,st,l) j1 j2 = ? ba nba t nt p np bl nbl bl2 nbl2 e ne h nh.
          (j1 = NonFinal (ba, t, p, bl, bl2, e, h))
       /\ (bl2 = []) /\ (bl2 = nbl2)
       /\ (COUNT_Auxiliary (qu,st,l) ba nba t nt p np bl nbl e ne h nh)
       /\ (!c. MEM c l ==>
                            ((MEM c h ==>
                             ?(l': ((cand list) # rat) list).
                               (l' = FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)
                            /\ (get_cand_pile c np = (get_cand_pile c p) ++ [l'])
                            /\ (get_cand_tally c nt = (get_cand_tally c t) + (SUM_RAT (l'))))
                            /\ (~ MEM c h ==>
                                           (get_cand_pile c np = get_cand_pile c p)
                                        /\ (get_cand_tally c nt = get_cand_tally c t))))
        /\ (j2 = NonFinal (nba, nt, np, nbl, nbl2, e, h)))`;
                   

(* ELECT rule *)

val ELECT_def = Define `
  ELECT ((qu,st,l):params) j1 j2 <=>
  (? ba nba t nt p np bl nbl bl2 nbl2 e ne h nh l1.
    (j1 = NonFinal (ba, t, p, bl, bl2, e, h))
     /\ (ELECT_Auxiliary (qu,st,l) ba t nt p np bl nbl bl2 nbl2 e ne h nh l1) 
     /\ (bl2 = [])
     /\ (nba = []) 
     /\ (nbl =  bl ++ l1)
     /\ (!c. MEM c l1 ==> (!l'. MEM (c,l') p ==> l' <> []))
     /\ (!c. MEM c l1 ==> (!l'. MEM (c,l') np ==> l' <> []))
     /\ (!c. MEM c l1 ==> (!l'. MEM (c,l') np ==>
                           let (PileCand_c = LAST (get_cand_pile c p))
                            in
                             let (Flat_l' = LAST l')
	                      in
                               (MAP FST Flat_l' = MAP FST PileCand_c)
                            /\ (MAP SND (Flat_l') = update_cand_transVal_ACT qu c t p)))
     /\ (j2 = NonFinal (nba, nt, np, nbl, nbl2, ne, nh)))`;
  
(* TRANSFER votes of Excluded candidates *)

val TRANSFER_EXCLUDED_def = Define `
    TRANSFER_EXCLUDED (qu,st,l) j1 j2 <=> TRANSFER_EXCLUDED_Auxiliary (qu,st,l) j1 j2`;

 
val _ = export_theory ();
