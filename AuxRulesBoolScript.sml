open preamble AuxSpecTheory AuxBoolTheory
  
val _ = new_theory "AuxRulesBool";

 
val ELIM_CAND_Auxiliary_dec_def = Define `
  (ELIM_CAND_Auxiliary_dec (c: cand) ((qu,st,l):params) (t: tallies)
                           (p: piles) (p': piles) (bl2: cand list) bl2' 
                           (e: cand list) (h: cand list) h') <=>  
     
              ((NULL bl2) \/ (~ NULL bl2 /\ (NULL (FLAT (get_cand_pile (HD bl2) p)))))
          (* /\ (NULL ba) 
           /\ (NULL bl)
           /\ (NULL bl') *) 
           /\ (LENGTH (e ++ h) > st) /\ (LENGTH e < st)
           /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
           /\ (list_MEM_dec (h++e) l)
           /\ (ALL_DISTINCT (h++e))
           /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
           /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
           /\ ALL_DISTINCT (MAP FST t)
           /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
           /\ (MEM c h)
           /\ (less_than_quota qu t h)
           /\ (h' = equal_except_dec c h)
           /\ (bigger_than_cand c t h)`;

(* /\ (bl2' = c :: bl2) :: this condition must be added to STVs such as Victoria and Tasmania *)

val TRANSFER_Auxiliary_dec_def = Define `
  (TRANSFER_Auxiliary_dec ((qu,st,l):params) (t: tallies)
                           (p: piles) (p': piles) (bl: cand list) (bl2: cand list) 
                           (e: cand list) (h: cand list))  ⇔
      ((NULL bl2) \/ (~ NULL bl2 /\ (NULL (FLAT (get_cand_pile (HD bl2) p)))))
(*   /\ (NULL ba) *) 
   /\ (LENGTH e < st)
   /\ (list_MEM_dec (h++e) l)
   /\ ALL_DISTINCT (h++e)
   /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
   /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
   /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (ALL_DISTINCT (MAP FST t))
   /\ (less_than_quota qu t h)
   /\ (~ NULL bl)`;
(* /\
  (TRANSFER_Auxiliary_dec _ (Final _) _ = F) /\
  (TRANSFER_Auxiliary_dec _ _ (Final _) = F)`; *)


val COUNT_Auxiliary_dec_def = Define `
   (COUNT_Auxiliary_dec ((qu, st, l): params) (ba: ballots) (ba': ballots) (t: tallies)
                         (t': tallies) (p: piles) (p': piles) (e: cand list) (h: cand list)) 
      (* (NonFinal (ba, t, p, bl, bl2, e, h))
       (NonFinal (ba', t', p', bl', bl2', e', h')) *) ⇔
   
       ALL_DISTINCT (h++e)
    /\ ALL_DISTINCT (MAP FST p)
    /\ (list_MEM_dec (h++e) l)
    /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
    /\ (Valid_PileTally_dec1 t' l) /\ (Valid_PileTally_dec2 t' l)
    /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
    /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
    /\ ALL_DISTINCT (MAP FST p')
    /\ ALL_DISTINCT (MAP FST t')
    /\ (~ NULL l) /\ (ALL_DISTINCT l)
    /\ ALL_DISTINCT (MAP FST t)
    /\ (~ NULL ba)
    /\ (~ NULL h)
    /\ (NULL ba')`;
(* /\
   (COUNT_Auxiliary_dec _ (Final _) _ = F) /\
   (COUNT_Auxiliary_dec _ _ (Final _) = F)`; *)


val ELECT_Auxiliary_dec = Define `
     (ELECT_Auxiliary_dec ((qu,st,l): params) (ba: ballots) (t: tallies)
                          (p: piles) (p': piles) bl bl' (e: cand list) e' (h: cand list) h'
       (*    (NonFinal (ba, t, p, bl, bl2, e, h))
           (NonFinal (ba', t', p', bl', bl2', e',h')) *) <=>
              let (l1 = (DROP (LENGTH bl) bl'))
                 in
                   (SORTED (tally_comparison t) l1)
                /\ ALL_DISTINCT (l1 ++ e)
                /\ (NULL ba) 
                /\ (~ NULL l1)
                /\ (bigger_than_quota l1 t qu)
                /\ (0 < qu)
                /\ (LENGTH (l1 ++ e) <= st)
                /\ (eqe_list_dec l1 h' h)
                /\ (eqe_list_dec2 l1 h' h)
                /\ ALL_DISTINCT h
                /\ ALL_DISTINCT (l1 ++ h')
                /\ ALL_DISTINCT e'
                /\ (eqe_list_dec l1 e e')
                /\ (eqe_list_dec2 l1 e e')
                /\ (piles_eq_list h l1 p p')
                /\ ALL_DISTINCT (MAP FST p)
                /\ ALL_DISTINCT (MAP FST t)
                /\ ALL_DISTINCT (MAP FST p')
                /\ (~ NULL l)
                /\ ALL_DISTINCT l
                /\ (bl = TAKE (LENGTH bl) bl') 
          (*      /\ (bl' = bl ++ l1) *)
                /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
                /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
                /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
                /\ (list_MEM_dec e' l)
                /\ (list_MEM_dec h l))`;
(* /\
     (ELECT_Auxiliary_dec _ (Final _) _ = F) /\
     (ELECT_Auxiliary_dec _ _ (Final _) = F)`; *)

val _ = export_theory ();
