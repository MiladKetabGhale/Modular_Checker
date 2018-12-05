open preamble AuxSpecTheory

val _ = new_theory "AuxBool";

(* TODO: move to HOL *)
val LRC_APPEND = Q.store_thm("LRC_APPEND",
  `∀l1 l2 x y.
   LRC R (l1 ++ l2) x y ⇔
   ∃z. LRC R l1 x z ∧ LRC R l2 z y`,
  Induct \\ rw[LRC_def] \\ metis_tac[])
(* -- *)
 

val equal_except_dec_def = Define `
     (equal_except_dec (c :cand) [] = [])
  /\ (equal_except_dec c (h::t) = (if c = h then t
                                  else h:: equal_except_dec c t)) `;

val Valid_PileTally_dec1_def = Define `
        (Valid_PileTally_dec1 [] (l: cand list) ⇔ T)
     /\ (Valid_PileTally_dec1 (h::t) l ⇔ (MEM (FST h) l) /\ (Valid_PileTally_dec1 t l)) `;


val Valid_PileTally_dec2_def = Define `
        (Valid_PileTally_dec2 t ([]: cand list) ⇔ T)
     /\ (Valid_PileTally_dec2 t (l0::ls) ⇔ if (MEM l0 (MAP FST t))
                                                then (Valid_PileTally_dec2 t ls)
                                           else F) `;

val _ = overload_on("list_MEM",``λl1 l2. set l1 ⊆ set l2``);
val _ = overload_on("list_not_MEM",``λl1 l2. DISJOINT (set l1) (set l2)``);

 
val list_MEM_dec_def = Define `
      (list_MEM_dec [] l ⇔ T)
   /\ (list_MEM_dec (h::t) l ⇔ (MEM h l) /\ (list_MEM_dec t l))`;
 
val less_than_quota_def = Define `
  less_than_quota qu l ls =
    EVERY (λh. get_cand_tally h l < qu) ls`;

val bigger_than_cand_def = Define `
  bigger_than_cand c t ls =
    EVERY (λh0. get_cand_tally c t <= get_cand_tally h0 t) ls`;   

val subpile1_BlMem_trans2_def = Define `
  (subpile1_BlMem_trans2 (p: piles) [] <=> T) /\
  (subpile1_BlMem_trans2 p (l0::ls) <=> MEM (l0, []) p /\ (subpile1_BlMem_trans2 p ls))`;   
 
val subpile1_backlog_trans2_def = Define `
    (subpile1_backlog_trans2 bl (p1: piles) (p2: piles)) <=>
      EVERY (λp. MEM (if MEM (FST p) bl then (FST p,[]) else p) p2) p1`;
 
val subpile2_backlog_trans2_def = Define`
    subpile2_backlog_trans2 bl (ps:piles) p1 ⇔
      EVERY (λp. if MEM (FST p) bl then T else MEM p p1) ps`; 

(* 
val subpile_MEM_def = Define `
    (subpile_MEM c p1 (ps: piles)) <=>
      EVERY (λp. if (~ (c = (FST p))) then MEM p p1 else T) ps`;
*)

val first_continuing_cand_dec_def = Define `
  (first_continuing_cand_dec (c:cand) ([]: cand list)  (h: cand list) ⇔ F) /\
  (first_continuing_cand_dec c (b0::bs) h =
    if (c = b0) then T
    else if (~ MEM b0 h) /\ (first_continuing_cand_dec c bs h) then T
    else F)`; 
  
val COUNTAux_dec_def = Define `
     (COUNTAux_dec p np t t' ba h [] <=> T)
  /\ (COUNTAux_dec p np t t' ba  h (l0::ls) <=>
      (let (l' = FILTER (λb. (first_continuing_cand_dec l0 (FST b) h)) ba)
       in
          if (MEM l0 h) then
                (get_cand_pile l0 np = (get_cand_pile l0 p) ++[l']) /\
                (get_cand_tally l0 t' = (get_cand_tally l0 t) + SUM_RAT (MAP SND l'))
           else
                (get_cand_pile l0 np = get_cand_pile l0 p) /\
                (get_cand_tally l0 t' = get_cand_tally l0 t)) /\
        (COUNTAux_dec p np t t' ba h ls))`;


val take_append_def = Define `
   (take_append (l0::ls) (h::t) = (take_append ls t)) ∧
   (take_append l1 _ = l1)`;

val eqe_list_dec_def = Define `
     (eqe_list_dec ([]: cand list) l1 l2 ⇔ list_MEM_dec l1 l2)
  /\ (eqe_list_dec (l0::ls) l1 l2 ⇔ (~ MEM l0 l1) /\ (MEM l0 l2) /\ eqe_list_dec ls l1 l2)`;


val eqe_list_dec2_def = Define `
    eqe_list_dec2 l0 l1 l = EVERY (\l'. MEM l' l0 \/ MEM l' l1) l`


val bigger_than_quota = Define `
  bigger_than_quota ls (t:tallies) (qu:rat) =
    EVERY (λl0. qu ≤ get_cand_tally l0 t) ls`;

(* this function takes two lists l1 and l and checks if the given piles p1 and p2 are equal for
   all of the members of l1 which do not belong to l *)
val piles_eq_list_def = Define `
     (piles_eq_list ([]: cand list) l p1 p2 = T)
  /\ (piles_eq_list (l0::ls) l p1 p2 =
          if ~ (MEM l0 l)
              then (get_cand_pile l0 p1 = get_cand_pile l0 p2) /\ (piles_eq_list ls l p1 p2)
          else (piles_eq_list ls l p1 p2))`; 
      
val update_cand_pile = Define `
          (update_cand_pile (qu: rat) t ([]: cand list) p1 p2 ⇔ T)
       /\ (update_cand_pile qu t (l0::ls) p1 p2 ⇔
            let Flat_pile2 = FLAT (get_cand_pile l0 p2)
	      in
	       let Flat_pile1 = FLAT (get_cand_pile l0 p1)
	        in
                 (MAP FST Flat_pile2 = MAP FST (Flat_pile1))
              /\ (MAP SND Flat_pile2 = update_cand_trans_val qu l0 t Flat_pile1) /\
                 update_cand_pile qu t ls p1 p2)`;


val _ = export_theory();
 
