open preamble 
     AuxSpecTheory 
     AuxRulesSpecTheory
     AuxRulesBoolTheory
     AuxRulesEquivProofsTheory
    
val _ = new_theory "VictoriaRulesSpec";

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
  EWIN ((qu,st,l):params) j1 j2 =
    ∃u t p bl e h bl2.
      (j1 = NonFinal (u, t, p, bl, bl2, e, h))
      /\ (j2 = Final e)
      /\ ((LENGTH e) = st)`;
    
(* HWIN rule *)

val HWIN_def = Define `
  HWIN ((qu,st,l):params) j1 j2 =
    ∃u t p bl e h bl2.
       (j1 = NonFinal (u, t, p, bl, bl2, e, h))
       /\ (j2 = Final (e++h))
       /\ ((LENGTH (e ++ h)) <= st)`;

(* ELIMINATION rule *)
  
val ELIM_CAND_def = Define `
  ELIM_CAND (c:cand) ((qu,st,l):params) j1 j2 <=>
    ?ba nba t p np bl nbl bl2 nbl2 e h nh.
     (j1 = NonFinal (ba, t, p, bl, bl2, e, h))
        /\ (ELIM_CAND_Auxiliary c (qu,st,l) t p np bl2 nbl2 e h nh)
        /\ (bl2 = [])  
        /\ ((FLAT (get_cand_pile c p) = [] ==> nbl2 = []) /\ (FLAT (get_cand_pile c p) <> [] ==> nbl2 = [c]))
        /\ (bl = []) /\ (nbl = [])
        /\ (ba = [])
        /\ (nba = [])
        /\ (!d'. (~ MEM d' [c] ==>
           (!l. (MEM (d',l) p ==> MEM (d',l) np)) /\ (!l. (MEM (d',l) np ==> MEM (d',l) p)))) /\
    (j2 = NonFinal (nba, t, np, nbl, nbl2, e, nh))`;
     
    
(* TRANSFER rule *)

val TRANSFER_def = Define `
  TRANSFER ((qu,st,l):params) j1 j2 <=>
    ? ba nba t p np bl nbl bl2 nbl2 e h.
     (j1 = NonFinal (ba, t, p, bl, bl2, e, h))
      /\ (TRANSFER_Auxiliary (qu,st,l) t p np bl bl2 e h)
      /\ (ba = []) /\ (bl2 = []) /\ (nbl2 = [])
      /\ ? l c.
              ((bl = c::l)
           /\ (nbl = l)
           /\ (nba = FLAT (get_cand_pile c p))
           /\ (MEM (c,[]) np)
           /\ (!d'. ((d' <> c) ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np)
                            /\ (MEM (d',l') np ==> MEM (d',l') p)))))
           /\ (j2 = NonFinal (nba, t, np, nbl, nbl2, e, h))`;

(* COUNT rule *)

val COUNT_def = Define `
         (COUNT (qu,st,l) j1 j2 = ? ba nba t nt p np bl nbl bl2 nbl2 e ne h nh.
          (j1 = NonFinal (ba, t, p, bl, bl2, e, h))
       /\ (bl2 = []) /\ (nbl2 = []) /\ (bl = nbl)
       /\ (nba = []) /\ (e = ne) /\ (h = nh)
       /\ (COUNT_Auxiliary (qu,st,l) ba nba t nt p np e h)
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
     /\ (ELECT_Auxiliary (qu,st,l) ba t p np bl nbl e ne h nh l1) 
     /\ (ba = []) /\ (nba = []) /\ (t = nt) /\ (bl2 = []) /\ (nbl2 = [])
     /\ (nbl =  bl ++ l1) 
     /\ (!c. MEM c l1 ==> (!l'. MEM (c,l') np ==>
                           let (PileCand_c = FLAT (get_cand_pile c p))
                            in
                             let (Flat_l' = FLAT l')
	                      in
                               (MAP FST Flat_l' = MAP FST PileCand_c)
                            /\ (MAP SND (Flat_l') = update_cand_trans_val qu c t PileCand_c)))
     /\ (j2 = NonFinal (nba, nt, np, nbl, nbl2, ne, nh)))`;



val TRANSFER_EXCLUDED_def = Define `
    TRANSFER_EXCLUDED (qu,st,l) j1 j2 <=> TRANSFER_EXCLUDED_Auxiliary (qu,st,l) j1 j2`;




(* TRANSFER votes of Excluded candidates *)

(* 
val TRANSFER_EXCLUDED_def = Define `
    TRANSFER_EXCLUDED (qu,st,l) j1 j2 <=>
      (? ba nba t nt p np bl nbl bl2 nbl2 e ne h nh.
          (j1 = NonFinal (ba,t,p,bl,bl2,e,h))
       /\ (TRANSFER_EXCLUDED_Auxiliary (qu,st,l) nba t p np bl2 nbl2 e h)
       /\ (ba = []) /\ (t = nt) /\ (e = ne) /\ (h = nh) /\ (bl = nbl)
       /\ (j2 = NonFinal (nba,nt,np,nbl,nbl2,ne,nh)))`;
*)  
 
val _ = export_theory ();
