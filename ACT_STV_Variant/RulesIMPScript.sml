open preamble AuxSpecTheory AuxIMPTheory AuxRulesSpecTheory AuxRulesIMPTheory
 
val _ = new_theory "RulesIMP";


val EWIN_dec_def = Define `
    EWIN_dec ((qu,st,l):params) j1 j2 <=> EWIN_Auxiliary_dec (qu,st,l) j1 j2`;

val HWIN_dec_def = Define `
    HWIN_dec ((qu,st,l):params) j1 j2 <=> HWIN_Auxiliary_dec (qu,st,l) j1 j2`;

  
val ELIM_CAND_dec_def = Define `
  (ELIM_CAND_dec c ((qu,st,l):params)
       (NonFinal (ba, t, p, bl, bl2, e, h))
       (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
       (ELIM_CAND_Auxiliary_dec c (qu,st,l) ba t t' p p' bl bl' bl2 e e' h h')
    /\ (NULL bl2')  
    /\ (ba' = FLAT (get_cand_pile c p))
    /\ (MEM (c,[]) p')
    /\ (subpile1 c p p') /\ (subpile2 c p' p))
   /\ (ELIM_CAND_dec c _ (Final _ ) _ = F)
   /\ (ELIM_CAND_dec c _ _ (Final _ ) = F)`;


val TRANSFER_dec_def = Define `
  (TRANSFER_dec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
         (TRANSFER_Auxiliary_dec (qu,st,l) ba t t' p p' bl bl2 bl2' e e' h h')
      /\ (case bl of [] => F | hbl::tbl =>
         (bl' = [])
         /\ (ba' = FLAT (get_cand_pile_list (hbl::tbl) p))
         /\ (subpile1_BlMem_trans2 p' (hbl::tbl))
         /\ (subpile1_backlog_trans2 (hbl::tbl)  p p') /\ (subpile2_backlog_trans2 (hbl::tbl) p' p))) ∧
  (TRANSFER_dec _ (Final _) _ = F) /\
  (TRANSFER_dec _ _ (Final _) = F)`;
 
  
val COUNT_dec_def = Define `
   (COUNT_dec ((qu, st, l): params)
       (NonFinal (ba, t, p, bl, bl2, e, h))
       (NonFinal (ba', t', p', bl', bl2', e', h')) ⇔
    (COUNTAux_dec p p' t t' ba h l)
    /\ (NULL bl2) /\ (bl2 = bl2')
    /\ (COUNT_Auxiliary_dec (qu,st,l) ba ba' t t' p p' bl bl' e e' h h')) /\
   (COUNT_dec _ (Final _) _ = F) /\
   (COUNT_dec _ _ (Final _) = F)`;


val ELECT_dec = Define `
     (ELECT_dec ((qu,st,l): params)
           (NonFinal (ba, t, p, bl, bl2, e, h))
           (NonFinal (ba', t', p', bl', bl2', e',h')) <=>
                   (ELECT_Auxiliary_dec (qu,st,l) ba t t' p p' bl bl' bl2 bl2' e e' h h' (DROP (LENGTH bl) bl'))
                /\ (bl2 = [])
                /\ (ba' = [])
                /\ (update_cand_pile qu t (DROP (LENGTH bl) bl') p p')) /\
     (ELECT_dec _ (Final _) _ = F) /\
     (ELECT_dec _ _ (Final _) = F)`;
 

val TRANSFER_EXCLUDED_dec_def = Define `
    TRANSFER_EXCLUDED_dec (qu,st,l) j1 j2  <=> TRANSFER_EXCLUDED_Auxiliary_dec (qu,st,l) j1 j2`;


val _ = export_theory ();


