 open preamble AuxSpecTheory AuxIMPTheory AuxRulesIMPTheory
      
val _ = new_theory "RulesIMP";


val EWIN_dec_def = Define `
    EWIN_dec ((qu,st,l):params) j1 j2 <=> EWIN_Auxiliary_dec (qu,st,l) j1 j2`;

val HWIN_dec_def = Define `
    HWIN_dec ((qu,st,l):params) j1 j2 <=> EWIN_Auxiliary_dec (qu,st,l) j1 j2`;
    
val ELIM_CAND_dec_def = Define `
  (ELIM_CAND_dec c ((qu,st,l):params)
       (NonFinal (ba, t, p, bl, bl2, e, h))
       (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
       (ELIM_CAND_Auxiliary_dec c (qu,st,l) ba t t' p p' bl bl' bl2 e e' h h')
    /\ (NULL bl2')
    /\ (ba' = FLAT (get_cand_pile c p))
    /\ (PILES_EQ p p' /\ (PILES_EQ p' p)))
   /\ (ELIM_CAND_dec c _ (Final _ ) _ = F)
   /\ (ELIM_CAND_dec c _ _ (Final _ ) = F)`;
   
val TRANSFER_dec_def = Define `
  (TRANSFER_dec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
         (TRANSFER_Auxiliary_dec (qu,st,l) ba t t' p p' bl bl2 bl2' e e' h h')
      /\ (case bl of [] => F | hbl::tbl =>
              (NULL bl')
	   /\ (NULL tbl)    
           /\ (ba' = APPEND_ALL p)
           /\ (~ NULL (get_cand_pile hbl p)))
           /\ (ALL_EMPTY p')
           /\ (List_Diff e' h' l)) ∧
  (TRANSFER_dec _ (Final _) _ = F) /\
  (TRANSFER_dec _ _ (Final _) = F)`;
    
val COUNT_dec_def = Define `
   (COUNT_dec ((qu, st, l): params)
       (NonFinal (ba, t, p, bl, bl2, e, h))
       (NonFinal (ba', t', p', bl', bl2', e', h')) ⇔
    (COUNTAux_dec p p' t t' ba h l)
    /\ (bl2 = bl2') /\ (NULL bl2) 
    /\ (COUNT_Auxiliary_dec (qu,st,l) ba ba' t t' p p' bl bl' e e' h h')) /\
   (COUNT_dec _ (Final _) _ = F) /\
   (COUNT_dec _ _ (Final _) = F)`;
 
val ELECT_dec = Define `
     (ELECT_dec ((qu,st,l): params)
           (NonFinal (ba, t, p, bl, bl2, e, h))
           (NonFinal (ba', t', p', bl', bl2', e',h')) <=>
                   (ELECT_Auxiliary_dec (qu,st,l) ba t t' p p' bl bl' bl2 bl2' e e' h h' (DROP (LENGTH bl) bl'))
                /\ (NULL bl2)
                /\ (NULL ba')
                /\ (NULL bl) /\ (LENGTH bl' = 1)) /\
     (ELECT_dec _ (Final _) _ = F) /\
     (ELECT_dec _ _ (Final _) = F)`;

val TRANSFER_EXCLUDED_dec_def = Define `
    TRANSFER_EXCLUDED_dec (qu,st,l) j1 j2  <=> TRANSFER_EXCLUDED_Auxiliary_dec (qu,st,l) j1 j2`;


val _ = export_theory ();
