open preamble AuxSpecTheory AuxBoolTheory
     
val _ = new_theory "AuxRulesBool";

 
val ELIM_CAND_Auxiliary_dec_def = Define `
  (ELIM_CAND_Auxiliary_dec (c: cand) ((qu,st,l):params) (t: tallies)
                           (p: piles) (p': piles) (bl2: cand list) bl2' 
                           (e: cand list) (h: cand list) h') <=>  
     
              (NULL bl2) 
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


val TRANSFER_Auxiliary_dec_def = Define `
  (TRANSFER_Auxiliary_dec ((qu,st,l):params) (t: tallies)
                           (p: piles) (p': piles) (bl: cand list) (bl2: cand list) 
                           (e: cand list) (h: cand list))  ⇔
      (NULL bl2) 
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


val COUNT_Auxiliary_dec_def = Define `
   (COUNT_Auxiliary_dec ((qu, st, l): params) (ba: ballots) (ba': ballots) (t: tallies)
                         (t': tallies) (p: piles) (p': piles) (e: cand list) (h: cand list))  ⇔
   
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

(*
val ELECT_Auxiliary_dec = Define `
     (ELECT_Auxiliary_dec ((qu,st,l): params) (ba: ballots) (t: tallies)
                          (p: piles) (p': piles) bl bl' (e: cand list) e' (h: cand list) h' <=>
               
                   (SORTED (tally_comparison t) (DROP (LENGTH bl) bl'))
                /\ ALL_DISTINCT ((DROP (LENGTH bl) bl') ++ e)
                /\ (NULL ba) 
                /\ (~ NULL (DROP (LENGTH bl) bl'))
                /\ (bigger_than_quota (DROP (LENGTH bl) bl') t qu)
                /\ (0 < qu)
                /\ (LENGTH ((DROP (LENGTH bl) bl') ++ e) <= st)
                /\ (eqe_list_dec (DROP (LENGTH bl) bl') h' h)
                /\ (eqe_list_dec2 (DROP (LENGTH bl) bl') h' h)
                /\ ALL_DISTINCT h
                /\ ALL_DISTINCT ((DROP (LENGTH bl) bl') ++ h')
                /\ ALL_DISTINCT e'
                /\ (eqe_list_dec (DROP (LENGTH bl) bl') e e')
                /\ (eqe_list_dec2 (DROP (LENGTH bl) bl') e e')
                /\ (piles_eq_list h (DROP (LENGTH bl) bl') p p')
                /\ ALL_DISTINCT (MAP FST p)
                /\ ALL_DISTINCT (MAP FST t)
                /\ ALL_DISTINCT (MAP FST p')
                /\ (~ NULL l)
                /\ ALL_DISTINCT l
                /\ (bl = TAKE (LENGTH bl) bl') 
                /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
                /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
                /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
                /\ (list_MEM_dec e' l)
                /\ (list_MEM_dec h l))`;

*)


val ELECT_Auxiliary_dec = Define `
     (ELECT_Auxiliary_dec ((qu,st,l): params) (ba: ballots) (t: tallies)
                          (p: piles) (p': piles) bl bl' (e: cand list) e' (h: cand list) h' l1 <=>
                   (l1 = DROP (LENGTH bl) bl')
                /\ (SORTED (tally_comparison t) l1)
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
                /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
                /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
                /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
                /\ (list_MEM_dec e' l)
                /\ (list_MEM_dec h l))`;

val TRANSFER_EXCLUDED_Auxiliary_dec_def = Define `
    (TRANSFER_EXCLUDED_Auxiliary_dec (qu,st,l)
          (NonFinal (ba,t,p,bl,bl2,e,h))
          (NonFinal (ba',t',p',bl',bl2',e',h')) <=>
          (NULL ba) /\ (t = t') /\ (e = e') /\ (h = h') /\ (bl = bl')
          /\
            (case bl2 of
                c :: ls =>
             ((case NULL (get_cand_pile c p') of
                T => (NULL bl2')
               |_ => (bl2' = bl2))
          /\ (LENGTH e) < st
          /\ (list_MEM_dec (h ++ e) l)
          /\ (ALL_DISTINCT (h ++ e)) /\ (ALL_DISTINCT (MAP FST p'))
          /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
          /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
          /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
          /\ (~ NULL l) /\ (ALL_DISTINCT l)
          /\ ALL_DISTINCT (MAP FST t)
          /\ (less_than_quota qu t h)
          /\ (let xs = ReGroup_Piles (QSORT3 (\x y. (SND x) <= (SND y)) (FLAT (get_cand_pile c p)))
               in
                 (case xs of 
                  [] => F
                 |_ => 
                    (ba' = LAST xs) /\ (MEM (c, (TAKE ((LENGTH xs) - 1) xs)) p')))
          /\ (subpile2_backlog_trans2 [c] p p') /\ (subpile2_backlog_trans2 [c] p' p))
         | _ => F)) /\
    (TRANSFER_EXCLUDED_Auxiliary_dec _ (Final _) _ = F) /\
    (TRANSFER_EXCLUDED_Auxiliary_dec _ _ (Final _) = F) `;

(*
val TRANSFER_EXCLUDED_Auxiliary__dec_def = Define `
       TRANSFER_EXCLUDED_Auxiliary_dec ((qu,st,l):params) ba' (t: tallies)
                           (p: piles) (p': piles) (bl2: cand list) bl2'
                           (e: cand list) (h: cand list) <=>
       case bl2 of
         c :: ls =>
             (case NULL (get_cand_pile c p') of
                T => (NULL bl2')
               |_ => (bl2' = bl2))
          /\ (LENGTH e) < st
          /\ (list_MEM_dec (h ++ e) l)
          /\ (ALL_DISTINCT (h ++ e)) /\ (ALL_DISTINCT (MAP FST p'))
          /\ (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)
          /\ (Valid_PileTally_dec1 p l) /\ (Valid_PileTally_dec2 p l)
          /\ (Valid_PileTally_dec1 p' l) /\ (Valid_PileTally_dec2 p' l)
          /\ (~ NULL l) /\ (ALL_DISTINCT l)
          /\ ALL_DISTINCT (MAP FST t)
          /\ (less_than_quota qu t h)
          /\ (let xs = ReGroup_Piles (QSORT3 (\x y. (SND x) <= (SND y)) (FLAT (get_cand_pile c p)))
               in
                 (ba' = LAST xs) /\ (MEM (c, (TAKE ((LENGTH xs) - 1) xs)) p'))
          /\ (subpile2_backlog_trans2 [c] p p') /\ (subpile2_backlog_trans2 [c] p' p)
         | _ => F `;
*) 
        
val _ = export_theory ();
