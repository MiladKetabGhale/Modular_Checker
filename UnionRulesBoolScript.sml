open preamble AuxSpecTheory AuxBoolTheory AuxRulesSpecTheory AuxRulesBoolTheory
  
val _ = new_theory "UnionRulesBool";


val EWIN_dec_def = Define `
  (EWIN_dec ((qu,st,l):params) (NonFinal (_,_,_,_,_,e,_)) (Final e')
     ⇔ (e = e') /\ LENGTH e = st) ∧
  (EWIN_dec _ _ _ ⇔ F)`;
 
val HWIN_dec_def = Define `
  (HWIN_dec ((qu,st,l):params) (NonFinal (_,_,_,_,_,e,h)) (Final e')
    ⇔ (e' = e ++ h) ∧ (LENGTH (e++h) ≤ st)) ∧
  (HWIN_dec _ _ _ = F)`;


val ELIM_CAND_dec_def = Define `
  (ELIM_CAND_dec c ((qu,st,l):params)
       (NonFinal (ba, t, p, bl, bl2, e, h))
       (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
       (ELIM_CAND_Auxiliary_dec c (qu,st,l) t p p' bl2' bl2 e h h')
    /\ (NULL bl2) /\ (NULL bl2') /\ (t = t') /\ (e = e')
    /\ (NULL bl) /\ (NULL bl') /\ (ba = [])
    /\ (h' = equal_except_dec c h)
    /\ (ba' = FLAT (get_cand_pile c p))
    /\ (MEM (c,[]) p')
    /\ (subpile1 c p p') /\ (subpile2 c p' p))
   /\ (ELIM_CAND_dec c _ (Final _ ) _ = F)
   /\ (ELIM_CAND_dec c _ _ (Final _ ) = F)`;


val TRANSFER_dec_def = Define `
  (TRANSFER_dec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
         (TRANSFER_Auxiliary_dec (qu,st,l) t p p' bl bl2 e h)
      /\ (NULL bl2) /\ (NULL bl2') /\ (NULL ba)
      /\ (h' = h) /\ (e = e') /\ (t = t')
      /\ (case bl of [] => F | hbl::tbl =>
              (bl' = tbl)
           /\ (ba' = FLAT (get_cand_pile hbl p))
           /\ (MEM (hbl,[]) p')
           /\ (subpile1 hbl p p') /\ (subpile2 hbl p' p))) ∧
  (TRANSFER_dec _ (Final _) _ = F) /\
  (TRANSFER_dec _ _ (Final _) = F)`;


val COUNT_dec_def = Define `
   (COUNT_dec ((qu, st, l): params)
       (NonFinal (ba, t, p, bl, bl2, e, h))
       (NonFinal (ba', t', p', bl', bl2', e', h')) ⇔
    (COUNTAux_dec p p' t t' ba h l)
    /\ (bl2 = bl2') /\ (NULL bl2) /\ (bl = bl')
    /\ (e = e') /\ (h = h') /\ (ba' = [])
    /\ (COUNT_Auxiliary_dec (qu,st,l) ba ba' t t' p p' e h)) /\
   (COUNT_dec _ (Final _) _ = F) /\
   (COUNT_dec _ _ (Final _) = F)`;


val ELECT_dec = Define `
     (ELECT_dec ((qu,st,l): params)
           (NonFinal (ba, t, p, bl, bl2, e, h))
           (NonFinal (ba', t', p', bl', bl2', e',h')) <=>
		   (ELECT_Auxiliary_dec (qu,st,l) ba t p p' bl bl' e e' h h')
                /\ (bl2 = bl2') /\ (bl2 = [])
                /\ (ba = []) /\ (ba' = [])
                /\ (t = t')
                /\ (update_cand_pile qu t (DROP (LENGTH bl) bl') p p')) /\
     (ELECT_dec _ (Final _) _ = F) /\
     (ELECT_dec _ _ (Final _) = F)`;

 
val TRANSFER_EXCLUDED_dec_def = Define `
    TRANSFER_EXCLUDED_dec (qu,st,l) j1 j2 <=> F`;
 
val _ = export_theory ();
