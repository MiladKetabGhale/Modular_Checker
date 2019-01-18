open preamble AuxSpecTheory AuxIMPTheory RulesSpecTheory AuxRulesIMPTheory
  
val _ = new_theory "RulesIMP";


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
       (*(NULL bl2) /\ (NULL bl2') /\ (NULL ba) /\ (e = e') /\ (h = h') /\ (t = t') *)
      (TRANSFER_Auxiliary_dec (qu,st,l) ba t t' p p' bl bl2 bl2' e e' h h')
  (* /\ (LENGTH e < st)
   /\ (list_MEM_dec (h++e) l)
   /\ ALL_DISTINCT (h++e)
   /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
   /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
   /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
   /\ (¬(NULL l)) /\ (ALL_DISTINCT l)
   /\ (ALL_DISTINCT (MAP FST t))
   /\ (less_than_quota qu t h) 
   /\ (ALL_DISTINCT (MAP FST p)) *)
   /\ (case bl of [] => F | hbl::tbl =>
         let gcp = get_cand_pile hbl p
           in
              (~ NULL gcp)
           /\ (MEM hbl l)
           /\ (bl' = tbl)
           /\ (ba' = LAST gcp)
           /\ (MEM (hbl,[]) p')
           /\ (subpile1 hbl p p') /\ (subpile2 hbl p' p))) ∧
  (TRANSFER_dec _ (Final _) _ = F) /\
  (TRANSFER_dec _ _ (Final _) = F)`;




(*
val TRANSFER_dec_def = Define `
  (TRANSFER_dec ((qu,st,l):params)
    (NonFinal (ba, t, p, bl, bl2, e, h))
    (NonFinal (ba', t', p', bl', bl2', e',h')) ⇔
         (TRANSFER_Auxiliary_dec (qu,st,l) t p p' bl bl2 e h)
      /\ (list_MEM_dec bl l)
      /\ (ALL_NON_EMPTY p bl)
      /\ (ALL_DISTINCT (MAP FST p))
      /\ (NULL bl2) /\ (NULL bl2') /\ (NULL ba)
      /\ (h' = h) /\ (e = e') /\ (t = t')
      /\ (case bl of [] => F | hbl::tbl =>
              (bl' = tbl)
           /\ (ba' = LAST (get_cand_pile hbl p))
           /\ (MEM (hbl,[]) p')
           /\ (subpile1 hbl p p') /\ (subpile2 hbl p' p))) ∧
  (TRANSFER_dec _ (Final _) _ = F) /\
  (TRANSFER_dec _ _ (Final _) = F)`;
*)

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
              let l1 = DROP (LENGTH bl) bl' 
                in
		   (ELECT_Auxiliary_dec (qu,st,l) ba t p p' bl bl' e e' h h' l1)
                /\ (bl2 = bl2') /\ (bl2 = [])
                /\ (ba = []) /\ (ba' = [])
                /\ (t = t')
                /\ (ALL_NON_EMPTY p l1)
         (*       /\ (ALL_NON_ZERO p l1) *)
                /\ (ALL_NON_EMPTY p' l1)
         (*       /\ (ALL_NON_ZERO p' l1) *)
                /\ (update_cand_pile_ACT qu t (DROP (LENGTH bl) bl') p p')) /\
     (ELECT_dec _ (Final _) _ = F) /\
     (ELECT_dec _ _ (Final _) = F)`;


val TRANSFER_EXCLUDED_dec_def = Define `
    TRANSFER_EXCLUDED_dec (qu,st,l) j1 j2  <=> TRANSFER_EXCLUDED_Auxiliary_dec (qu,st,l) j1 j2`;



(* 
val TRANSFER_EXCLUDED_dec_def = Define `
    (TRANSFER_EXCLUDED_dec (qu,st,l) 
          (NonFinal (ba,t,p,bl,bl2,e,h))
          (NonFinal (ba',t',p',bl',bl2',e',h')) <=> 
                   (TRANSFER_EXCLUDED_Auxiliary_dec (qu,st,l) ba' t p p' bl2 bl2' e h) 
                /\ (NULL ba) /\ (t = t') /\ (e = e') /\ (h = h') /\ (bl = bl') /\ F) /\
    (TRANSFER_EXCLUDED_dec _ (Final _) _ = F) /\ 
    (TRANSFER_EXCLUDED_dec _ _ (Final _) = F) `;
*)
 
val _ = export_theory ();
