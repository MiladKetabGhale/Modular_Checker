open preamble AuxSpecTheory AuxBoolTheory ratTheory 
               
val _ = new_theory "AuxEquivProofs";


val LRC_APPEND = Q.store_thm("LRC_APPEND",
  `∀l1 l2 x y.
   LRC R (l1 ++ l2) x y ⇔
   ∃z. LRC R l1 x z ∧ LRC R l2 z y`,
  Induct \\ rw[LRC_def] \\ metis_tac[]);


val list_MEM_dec_thm = Q.store_thm("list_MEM_dec_thm",
 `list_MEM_dec = list_MEM`,
   simp[FUN_EQ_THM]
   \\ Induct \\ rw[list_MEM_dec_def]);

val GET_CAND_TALLY_HEAD_REMOVAL_def = Q.store_thm ("GET_CAND_TALLY_HEAD_REM",
`!(h: cand #rat) t c. (~(c = FST h)) ==> (get_cand_tally c (h::t) = get_cand_tally c t)`,
          Induct_on `t `
               >- (rw[get_cand_tally_def] >>
                   Cases_on`h` >> fs[ALOOKUP_def])

               >- (REPEAT STRIP_TAC
                 >> first_assum (qspecl_then [`h`,`c`] strip_assume_tac)
                    >> rw[get_cand_tally_def] >>
                    Cases_on`h'` >> fs[ALOOKUP_def]))
 
val GET_CAND_TALLY_MEM2 = Q.store_thm ("GET_CAND_TALLY_MEM",
 `!(t: (cand #rat) list) c. (MEM c (MAP FST t))
                                    ==> (MEM (c, get_cand_tally c t) t) `,

    Induct_on `t`
        >- rw []
 
        >- ((REPEAT STRIP_TAC >> Cases_on `h` >> Cases_on `c =q`)
          >- fs[get_cand_tally_def,ALOOKUP_def]
	  >- fs[get_cand_tally_def,ALOOKUP_def]));
  
val PileTally_to_PileTally_DEC1 = Q.store_thm ("PileTally_to_PileTally_DEC1",
 `!l t. (!c. (MEM c (MAP FST t)) ==> (MEM c l)) ==> (Valid_PileTally_dec1 t l) `,

    Induct_on `t`
       >- rw [Valid_PileTally_dec1_def]
       >- (REPEAT STRIP_TAC
          >> first_assum (qspecl_then [`FST h`] strip_assume_tac)
            >> rfs[Valid_PileTally_dec1_def,MAP]));
  
val PileTally_DEC1_to_PileTally = Q.store_thm ("PileTally_DEC1_to_PileTally",
 `!l t. (Valid_PileTally_dec1 t l) ==> (!c. MEM c (MAP FST t) ==> (MEM c l))`,

    Induct_on `t`
        >- rw[]
        >- (REPEAT STRIP_TAC
            >> rfs [Valid_PileTally_dec1_def]));
  
val PileTally_to_PileTally_DEC2 = Q.store_thm ("PileTally_to_PileTally_DEC2",
   `!l t. (!c. (MEM c l) ==> (MEM c (MAP FST t))) ==> (Valid_PileTally_dec2 t l) `,

     Induct_on `l`
        >- rw [Valid_PileTally_dec2_def]
        >- rfs [Valid_PileTally_dec2_def]);
 

val PileTally_DEC2_IMP_PileTally = Q.store_thm ("PileTally_DEC2_IMP_PileTally",
  `!l t. (Valid_PileTally_dec2 t l) ==> (!c. (MEM c l) ==> (MEM c (MAP FST t)))`,

      Induct_on `l`
         >- rw []
         >- ((REPEAT STRIP_TAC
           >> FULL_SIMP_TAC list_ss [MEM])
              >- FULL_SIMP_TAC list_ss [Valid_PileTally_dec2_def]
              >- rfs [Valid_PileTally_dec2_def]));
    
val Valid_PileTally_Spec_iff_Valid_PileTally_DEC = Q.store_thm ("Valid_PileTally_Spec_iff_Valid_PileTally_DEC",
 `!l t. Valid_PileTally t l <=> (Valid_PileTally_dec1 t l) /\ (Valid_PileTally_dec2 t l)`,
   metis_tac[Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,PileTally_DEC2_IMP_PileTally]);
     
val REMOVE_ONE_CAND_APPEND = Q.store_thm ("REMOVE_ONE_CAND_APPEND",
 `! l1 l2 (c: cand). (~ MEM c l1) ==> (equal_except_dec c (l1 ++l2) = l1 ++ (equal_except_dec c l2))`,

   Induct_on `l1`
       >- RW_TAC list_ss [APPEND_NIL,equal_except_dec_def]
       >- (REPEAT STRIP_TAC
         >> first_assum (qspecl_then [`l2`,`c`] strip_assume_tac)
           >> FULL_SIMP_TAC list_ss [MEM,equal_except_dec_def]));
 
val REMOVE_ONE_CAND_NOTIN = Q.store_thm ("REMOVE_ONE_CAND_NOTIN",
 `!l (c: cand). (~ MEM c l) ==> (equal_except_dec c l = l) `,

    Induct_on `l`
        >- rw [equal_except_dec_def]
        >- (REPEAT STRIP_TAC
          >> FULL_SIMP_TAC list_ss [MEM, equal_except_dec_def])) ;
 
val EQE_REMOVE_ONE_CAND = Q.store_thm ("EQE_REMOVE_ONE_CAND",
  `!h (c: cand). (MEM c h) /\ (ALL_DISTINCT h) ==> (equal_except c (equal_except_dec c h) h) `,

 Induct_on `h`

   >-  rw[]
   >-  ((REPEAT STRIP_TAC
      >> Cases_on `c= h'`)
        >- (rw[equal_except_dec_def,equal_except_def]
          >> MAP_EVERY qexists_tac [`[]`,`h`]
	  >> FULL_SIMP_TAC list_ss [ALL_DISTINCT])
        >-  ((rw[equal_except_dec_def,equal_except_def]
           >> `ALL_DISTINCT h` by fs[ALL_DISTINCT]
            >> `equal_except c (equal_except_dec c h) h` by metis_tac [ALL_DISTINCT,MEM]
             >> rfs[equal_except_def])
              >-  rw[]
              >- (MAP_EVERY qexists_tac [`h'::l1`,`l2`]
                >> FULL_SIMP_TAC list_ss []))));
 
val EQE_IMP_REMOVE_ONE_CAND = Q.store_thm ("EQE_IMP_REMOVE_ONE_CAND",
 `!h1 h2 (c: cand). (MEM c h2) /\ (equal_except c h1 h2) ==> (h1 = equal_except_dec c h2) `,

   FULL_SIMP_TAC list_ss [equal_except_def]
    >> REPEAT STRIP_TAC
     >>  ASSUME_TAC REMOVE_ONE_CAND_APPEND
         >> first_assum (qspecl_then [`l1`,`[c]++l2`,`c`] strip_assume_tac)
             >> rfs [equal_except_dec_def]);
 
val APPEND_NIL_LEFT = Q.store_thm ("APPEND_NIL_LEFT",
                                                `!l. [] ++ l = l `,
                                                       STRIP_TAC >> EVAL_TAC) ;

val APPEND_NIL_LEFT_COR = Q.store_thm("APPEND_NIL_lEFT_COR",
                                             `!h t. [] ++ (h::t) = h::t `,
                                                   rw[APPEND_NIL_LEFT]) ;
 

val MAP_APPEND_TRIO = Q.store_thm ("MAP_APPEND_TRIO",
  `!t l1 l0 l2. (t = l1 ++ [l0] ++ l2) ==> (MAP FST t = (MAP FST l1) ++ [FST l0] ++ (MAP FST l2))`,

     REPEAT STRIP_TAC
          >> `l1 ++ [l0] ++ l2 = l1 ++([l0] ++ l2)` by FULL_SIMP_TAC list_ss [APPEND_ASSOC]
            >> RW_TAC bool_ss []
              >> rfs [MAP_APPEND]);

val NoDupCand_BOTH_SIDES= Q.store_thm ("NoDupCand_BOTH_SIDES",
 `!l1 l2 (c:cand) (h1: cand list) h2. (l1 ++ [c] ++ l2 = h1 ++ [c] ++ h2)
                                      /\ (~ MEM c h1) /\ (~ MEM c h2) ==> (~ MEM c l1) `,

    Induct_on `l1`
         >- rw []
         >- ((REPEAT STRIP_TAC >>
               Cases_on `h1`)
               >- (rfs[APPEND,CONS_11]
                    >> RW_TAC bool_ss []
                      >> rfs[])
               >- (rfs[CONS_11]
                    >> first_assum (qspecl_then [`l2`,`c`,`t`,`h2`] strip_assume_tac)
                      >> rfs[])));
  
val get_cand_tally_APPEND = Q.store_thm ("get_cand_tally_APPEND",
  `!(l1: (cand #rat) list) l2 c. (~ MEM c (MAP FST l1))
                                  ==> (get_cand_tally c (l1++l2) = get_cand_tally c l2) `,

      Induct_on `l1`
           >- rw[APPEND_NIL,get_cand_tally_def] >>
	      Cases_on `h`
           >- (REPEAT STRIP_TAC >>
               `c <> q` by fs[MEM,MAP] >>
               fs[get_cand_tally_def,ALOOKUP_def]))


val EVERY_CAND_HAS_ONE_TALLY = Q.store_thm ("EVERY_CAND_HAS_ONE_TALLY",
  `!t c (x: rat). (ALL_DISTINCT (MAP FST t)) /\ (MEM (c,x) t) ==> (get_cand_tally c t = x) `,

      REPEAT STRIP_TAC
           >>  FULL_SIMP_TAC list_ss [MEM_SPLIT]
               >>
               ASSUME_TAC (INST_TYPE [alpha |-> ``:cand``] ALL_DISTINCT_APPEND)
               >> first_assum (qspecl_then [`MAP FST l1`,`MAP FST ([(c,x)] ++ l2)`] strip_assume_tac)
               >> `ALL_DISTINCT ((MAP FST l1) ++ (MAP FST ([(c,x)] ++ l2)))`
	        by FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND, MAP_APPEND]
               >> `!e. MEM e (MAP FST l1) ==> (~ MEM e (MAP FST ([(c,x)] ++ l2)))` by metis_tac[]
               >> `MEM c (MAP FST ([(c,x)] ++ l2))` by FULL_SIMP_TAC list_ss [MAP_APPEND]
               >> `~ MEM c (MAP FST l1)` by metis_tac[]
	       >> fs[get_cand_tally_APPEND,get_cand_tally_def,ALOOKUP_def])
 
val LESS_THAN_QUOTA_OK = Q.store_thm ("LESS_THAN_QUOTA_OK",
`!qu t0 t1 h. (less_than_quota qu (t0::t1) h) ==> (!c.(MEM c h) ==> (get_cand_tally c (t0::t1) < qu))`,

    Induct_on `h`
       >- rw []
       >- (REPEAT STRIP_TAC
         >> FULL_SIMP_TAC list_ss [MEM,less_than_quota_def,get_cand_tally_def]));
 
val less_than_qu_IMP_LogicalLessThanQuota = Q.store_thm ("less_than_qu_IMP_LogicalLessThanQuota",
 `!h t0 t1 (qu:rat). (less_than_quota qu (t0::t1) h) /\ (Valid_PileTally_dec2 (t0::t1) h) ==>
           (!c. (MEM c h) ==> ?x. (MEM (c,x) (t0::t1)) /\ (x < qu))`,

       Induct_on `h`
          >- rw []
          >- ((REPEAT STRIP_TAC
            >> FULL_SIMP_TAC bool_ss [MEM])
             >- ((ASSUME_TAC (INST_TYPE [alpha |-> ``:rat``] PileTally_DEC2_IMP_PileTally)
                >> first_x_assum (qspecl_then [`h'::h`,`t0::t1`] strip_assume_tac)
                  >> `!c. MEM c (h'::h) ==> (MEM c (MAP FST (t0::t1))) ` by metis_tac []
                     >> `!(h: (cand#rat)) t c. (MEM c (MAP FST (h::t)))
                                 ==> (MEM (c,get_cand_tally c (h::t)) (h::t))`
                        by (ASSUME_TAC GET_CAND_TALLY_MEM2
                         >> REPEAT STRIP_TAC
                         >> first_x_assum (qspecl_then [`h''::t`,`c'`] strip_assume_tac)
                         >> rw [])
                          >> first_assum (qspecl_then [`h'`] strip_assume_tac)
                            >> first_assum (qspecl_then [`t0`,`t1`,`h'`] strip_assume_tac) >> rfs[])
                             >- (qexists_tac `get_cand_tally h' (t0::t1)`
                               >> rfs [less_than_quota_def])
                             >- (qexists_tac `get_cand_tally h' (t0::t1)`
                              >> rw [] >> ASSUME_TAC LESS_THAN_QUOTA_OK
                               >> first_x_assum (qspecl_then [`qu`,`t0`,`t1`,`c::h`] strip_assume_tac)
                                >> rfs []))
             >- (first_assum (qspecl_then [`t0`,`t1`,`qu`] strip_assume_tac)
               >> rfs [less_than_quota_def,Valid_PileTally_dec2_def])));
 
val LogicalLessThanQu_IMP_less_than_quota =Q.store_thm ("LogicalLessThanQu_IMP_less_than_quota",
  `!(qu:rat) t h. (!c. (MEM c h) ==> ?x. (MEM (c,x) t)
                                       /\ (x < qu)) /\ (ALL_DISTINCT (MAP FST t))
                                       /\ (!c''. (MEM c'' h) ==> (MEM c'' (MAP FST t)))
                                   ==> (less_than_quota qu t h)`,

   Induct_on `h`
     >- rw [less_than_quota_def]
     >- ((REPEAT STRIP_TAC >>
        rw[less_than_quota_def])
          >- (`?x. (MEM (h',x) t) /\ (x < qu)` by metis_tac[MEM]
           >> `MEM h' (MAP FST t)` by metis_tac[MEM]
             >> `MEM (h', get_cand_tally h' t) t` by metis_tac [GET_CAND_TALLY_MEM2]
                 >> ASSUME_TAC EVERY_CAND_HAS_ONE_TALLY
                 >> `get_cand_tally h' t = x` by rfs [EVERY_CAND_HAS_ONE_TALLY]
                   >> metis_tac [])
        >- (`less_than_quota qu t h` by  metis_tac[MEM]
           >> fs[less_than_quota_def])))
 
val bigger_than_cand_OK = Q.store_thm ("bigger_than_cand_OK",
 `!c t h. (bigger_than_cand c t h) ==> (!d. (MEM d h) ==> (get_cand_tally c t <= get_cand_tally d t))`,

      Induct_on `h`
          >- rw []
          >- (REPEAT STRIP_TAC
            >> FULL_SIMP_TAC list_ss [MEM,bigger_than_cand_def]));

val bigger_than_cand_LogicallyOK = Q.store_thm ("bigger_than_cand_LogicallyOK",
 `!h (t0: cand #rat) t1 c. (bigger_than_cand c (t0::t1) h)
                        /\ (Valid_PileTally_dec2 (t0::t1) h) /\ (MEM c h) ==>
   (!d. (MEM d h)  ==> (?x (y: rat). (MEM (c,x) (t0::t1)) /\ (MEM (d,y) (t0::t1)) /\ (x <= y)))`,

     Induct_on `h`
        >- rw []
        >- (REPEAT STRIP_TAC
          >> ASSUME_TAC (INST_TYPE [alpha |-> ``:rat``] PileTally_DEC2_IMP_PileTally)
            >> first_assum (qspecl_then [`h'::h`,`t0::t1`] strip_assume_tac)
              >> `!c'. (MEM c' (h'::h)) ==> (MEM c' (MAP FST (t0::t1)))` by metis_tac []
                >> first_assum (qspecl_then [`c`] strip_assume_tac)
                  >> first_assum (qspecl_then [`d`] strip_assume_tac)
                    >> `MEM (c,get_cand_tally c (t0::t1)) (t0::t1)` by rfs [GET_CAND_TALLY_MEM2,MEM]
                      >> `MEM (d,get_cand_tally d (t0::t1)) (t0::t1)` by rfs [GET_CAND_TALLY_MEM2,MEM]
                       >> MAP_EVERY qexists_tac [`get_cand_tally c (t0::t1)`,`get_cand_tally d (t0::t1)`]
                         >> RW_TAC list_ss []
                           >> ASSUME_TAC bigger_than_cand_OK
                             >> first_assum (qspecl_then [`c`,`t0::t1`,`h'::h`] strip_assume_tac)
                               >> metis_tac []));
  
val Logical_bigger_than_cand_IMP_TheFunctional = Q.store_thm ("Logical_bigger_than_cand_IMP_TheFunctional",
 `!h t c. (!d. (MEM d h)  ==> (?x (y: rat). (MEM (c,x) t)
                                                  /\ (MEM (d,y) t) /\ (x <= y)))
                                                  /\ (ALL_DISTINCT (MAP FST t))
                                                  /\ (MEM c (MAP FST t))
                                                  /\ (!d''. (MEM d'' h) ==> (MEM d'' (MAP FST t)))
                                                 ==> (bigger_than_cand c t h)`,

    Induct_on `h`
        >- rw [bigger_than_cand_def]
        >- ((REPEAT STRIP_TAC
             >> rw[bigger_than_cand_def])
               >-( `?x y. (MEM (c,x) t) /\ (MEM (h',y) t) /\ (x <= y) ` by metis_tac [MEM]
                >> `MEM c (MAP FST t)` by metis_tac [MEM]
                 >> `MEM (c,get_cand_tally c t) t` by metis_tac [GET_CAND_TALLY_MEM2]
                   >> ASSUME_TAC EVERY_CAND_HAS_ONE_TALLY
                   >> `x = get_cand_tally c t` by rfs []
                    >> `MEM h' (MAP FST t)` by metis_tac [MEM]
                     >> `MEM (h',get_cand_tally h' t) t` by metis_tac [GET_CAND_TALLY_MEM2]
                      >> `y = get_cand_tally h' t ` by rfs []
                       >> RW_TAC bool_ss [])
             >-( first_assum(qspecl_then [`t`,`c`] strip_assume_tac)
               >> rfs[bigger_than_cand_def,MEM])));

val SUBPILE_ONE_HEAD_REMOVAL = Q.store_thm ("SUBPILE_ONE_HEAD_REMOVAL",
 `! p1 p2 c h. (subpile1 c (h::p1) p2) ==> (subpile1 c p1 p2)`,
  rw[subpile1_def]);
 

val Functional_subpile1_IMP_TheLogical = Q.store_thm ("Functional_subpile1_IMP_TheLogical",
 `!p1 p2 c. (subpile1 c p1 p2) ==>  (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p1 ==> MEM (d',l) p2))))`,

     Induct_on `p1`
        >- rw[]
        >- ((REPEAT STRIP_TAC
          >> FULL_SIMP_TAC list_ss [MEM])
            >- (`d' = FST h` by RW_TAC bool_ss [PAIR_EQ,FST]
              >> `c <> FST h` by RW_TAC bool_ss []
                >> FULL_SIMP_TAC list_ss [subpile1_def])
            >- (first_assum (qspecl_then [`p2`,`c`] strip_assume_tac)
              >> metis_tac[SUBPILE_ONE_HEAD_REMOVAL])));
 
 
val GET_CAND_PILE_MEM = Q.store_thm ("GET_CAND_PILE_MEM",
 `!(p:piles) c. (MEM c (MAP FST p))
                          ==> (MEM (c,get_cand_pile c p) p)`,

        Induct_on `p`
             >-  rw []
               >- ((REPEAT STRIP_TAC
                 >>Cases_on `c = FST h`)
                   >- (Cases_on `h`
                    >> fs[get_cand_pile_def,ALOOKUP_def,MEM])
                   >- (Cases_on `h`
                    >> rfs [get_cand_pile_def,ALOOKUP_def,MEM,MAP]
                     >> rw[])));
 
val get_cand_pile_APPEND = Q.store_thm ("get_cand_pile_APPEND",
 `! (l1: piles) l2 c. (~ MEM c (MAP FST l1))
                           ==> (get_cand_pile c (l1++l2) = get_cand_pile c l2)`,

     Induct_on `l1`
        >-  rw []
        >- (REPEAT STRIP_TAC >>
	      Cases_on `h` >> FULL_SIMP_TAC list_ss [ALOOKUP_def,MEM,MAP,get_cand_pile_def]));
 
val EVERY_CAND_HAS_ONE_PILE = Q.store_thm ("EVERY_CAND_HAS_ONE_PILE",
 `! p c (y: (((cand list) # rat) list) list). (ALL_DISTINCT (MAP FST p)) /\ (MEM (c,y) p)
                          ==> (get_cand_pile c p = y)`,

      (REPEAT STRIP_TAC
      >> FULL_SIMP_TAC list_ss [MEM_SPLIT]

               >> ASSUME_TAC (INST_TYPE [alpha |-> ``:cand``] ALL_DISTINCT_APPEND)
               >> first_assum (qspecl_then [`MAP FST l1`,`MAP FST ([(c,x)] ++ l2)`] strip_assume_tac)
               >> `ALL_DISTINCT ((MAP FST l1) ++ (MAP FST ([(c,x)] ++ l2)))`
	        by FULL_SIMP_TAC list_ss [ALL_DISTINCT_APPEND, MAP_APPEND]
               >> `!e. MEM e (MAP FST l1) ==> (~ MEM e (MAP FST ([(c,x)] ++ l2)))` by metis_tac[]
               >> `MEM c (MAP FST ([(c,x)] ++ l2))` by FULL_SIMP_TAC list_ss [MAP_APPEND]
               >> `~ MEM c (MAP FST l1)` by metis_tac[]
               >> ASSUME_TAC get_cand_pile_APPEND
               >> first_assum (qspecl_then [`l1`,`(c,y)::l2`] strip_assume_tac)
               >>  fs [get_cand_pile_def,get_cand_pile_APPEND,ALOOKUP_def]));
  

val Logical_subpile1_IMP_TheFunctional = Q.store_thm ("Logical_subpile1_IMP_TheFunctional",
 `! p1 p2 c. (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p1 ==> MEM (d',l) p2)))
                /\ ((d' = c) ==> (MEM (c,[]) p2))) ==> (subpile1 c p1 p2)`,

         Induct_on `p1`
           >- rw[subpile1_def]
           >- ((REPEAT STRIP_TAC
             >>  rw[subpile1_def])
               >-( Cases_on `c = FST h`
                   >- RW_TAC bool_ss []
                   >- (first_assum (qspecl_then [`FST h`] strip_assume_tac)
		       >> fs[]))
          >- rfs[subpile1_def]

          >- (first_assum (qspecl_then [`FST h`] strip_assume_tac)
            >> rfs[]
            >> ` (FST h,SND h) = h` by rfs[PAIR]
             >> `MEM (FST h, SND h) p2` by metis_tac[PAIR,PAIR_EQ]
               >> fs[])

           >- rfs[subpile1_def]));
 
val SUBPILE_TWO_HEAD_REMOVAL = Q.store_thm ("SUBPILE_TWO_HEAD_REMOVAL",
 `!p1 p2 c h. (subpile2 c (h::p2) p1) ==> (subpile2 c p2 p1) `,
 rw[subpile2_def]);

 
val Functional_subpile2_IMP_TheLogical = Q.store_thm ("Functional_subpile2_IMP_TheLogical",
 `!p1 p2 c. (subpile2 c p2 p1) ==>  (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p2 ==> MEM (d',l) p1))))`,

    Induct_on `p2`
        >- rw []
        >- ((REPEAT STRIP_TAC
          >> FULL_SIMP_TAC bool_ss [MEM])
             >- (`d' = FST h` by RW_TAC bool_ss [PAIR_EQ,FST]
               >> `c <> FST h` by RW_TAC bool_ss []
                 >>  RW_TAC bool_ss [subpile2_def]
                   >> FULL_SIMP_TAC list_ss [subpile2_def])
             >- (first_assum (qspecl_then [`p1`,`c`] strip_assume_tac)
               >> metis_tac [SUBPILE_TWO_HEAD_REMOVAL])));
 

val subpile1_CandPile_Empty = Q.store_thm ("subpile1_CandPile_Empty",
 `!(l: cand list) p1 p2 c. (subpile1 c p1 p2) /\ (MEM c (MAP FST p2))
                                              /\ (MEM c (MAP FST p1))  ==> (MEM (c,[]) p2)`,

Induct_on `p1`
     >- rw[]
   >- ((REPEAT STRIP_TAC
          >> Cases_on `c = FST h`)
          >- (FULL_SIMP_TAC list_ss [subpile1_def]
              >> metis_tac [subpile1_def,MAP,MEM])
         >- fs[subpile1_def,MEM]));

val Logical_subpile2_IMP_TheFunctional = Q.store_thm ("Logical_subpile2_IMP_TheFunctional",
 `!p1 p2 c. (!d'. ((d' <> c) ==> (!l. (MEM (d',l) p2 ==> MEM (d',l) p1)))
              /\ ((d' = c) ==> (?l. MEM (c,l) p1))) ==> (subpile2 c p2 p1)`,

      Induct_on `p2`
           >-   rw[subpile2_def]
           >- ((REPEAT STRIP_TAC
	       >> Cases_on `c = FST h`)
                 >-  fs [subpile2_def]
                 >- (fs [subpile2_def]
                     >> first_assum(qspecl_then [`FST h`] strip_assume_tac)
                       >> rfs[]
                        >> `MEM (FST h,SND h) p1` by rfs[PAIR,PAIR_EQ]
                          >> metis_tac[PAIR,PAIR_EQ])));
  
val logical_GetCandPile_IMP_TheFunctional = Q.store_thm ("logical_GetCandPile_IMP_TheFunctional",
 `!(p: piles) nba c. (!d. (d <> c) ==>
   (!l. MEM (d,l) p ==> ~ ((d,l) = (d,nba)))) /\ (!d. (d = c) ==> (!l. MEM (c,l) p /\ ((c,l) = (c,nba))))
/\ MEM c (MAP FST p) ==> (nba = get_cand_pile c p)`,

    Induct_on `p`
        >- rw[]
        >- ((REPEAT STRIP_TAC >>
	     Cases_on `c = FSt h`)
               >- (ASSUME_TAC GET_CAND_PILE_MEM
                 >> first_assum (qspecl_then [`h::p`,`c`] strip_assume_tac)
                   >> `MEM (c,get_cand_pile c (h::p)) (h::p)` by metis_tac[]
                     >> `(c,get_cand_pile c (h::p)) =  (c,nba)` by metis_tac[]
                       >> RW_TAC bool_ss [PAIR_EQ,EQ_SYM_EQ])
            >- metis_tac[MEM,MAP,PAIR_EQ,EQ_SYM_EQ]));
  
val list_not_MEM_verified_fully= Q.store_thm ("list_not_MEM_verified_fully",
 `!l1 (l2: cand list). (!c. MEM c l1 ==> (~ MEM c l2)) <=> (list_not_MEM l1 l2)`,

        Induct_on `l1`
             >- rw[]
             >- (REPEAT STRIP_TAC
	          >> fs[]
                    >> metis_tac[MEM]));


val Logical_list_MEM_VICE_VERCA_TheFunctional = Q.store_thm("Logical_list_MEM_VICE_VERCA_TheFunctional",
 `!(l1: cand list) l2. (!c. MEM c l1 ==> MEM c l2) <=> list_MEM_dec l1 l2`,

    Induct_on `l1`
      >-  fs[list_MEM_dec_def]
      >- (REPEAT STRIP_TAC >> fs[]
        >> metis_tac[MEM,list_MEM_dec_def]));

 
val fcc_to_first_continuing_cand = Q.store_thm ("fcc_to_first_continuing_cand",
 `! c b h. first_continuing_cand_dec c b h ==> first_continuing_cand c b h`,

  Induct_on `b`
    >- rw[first_continuing_cand_dec_def]
    >- ((REPEAT STRIP_TAC
      >>  rw[first_continuing_cand_def]
       >> Cases_on `c = h`)
         >- (MAP_EVERY qexists_tac [`[]`,`b`]
          >> FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT])
         >- (rfs [first_continuing_cand_dec_def]
           >- RW_TAC bool_ss []
           >- (rfs [first_continuing_cand_def]
            >> `?L1 L2. (b = L1 ++ [c]++L2) /\ (!d. MEM d L1 ==> ~ MEM d h')` by metis_tac[]
             >> MAP_EVERY qexists_tac [`h::L1`,`L2`]
              >> FULL_SIMP_TAC list_ss [MEM] >> metis_tac [MEM]))));
  
 
 val first_continuing_cand_IMP_fcc = Q.store_thm ("first_continuing_cand_IMP_fcc",
 `! c b h. first_continuing_cand c b h ==> first_continuing_cand_dec c b h`,

Induct_on `b`

>- rw[first_continuing_cand_def]
>- ((REPEAT STRIP_TAC
  >> rw[first_continuing_cand_dec_def]
    >> Cases_on `c = h`)
      >- RW_TAC bool_ss []
      >- ((rfs [first_continuing_cand_def]
      >> `(l1 = []) \/ (?L1 x. l1 = x::L1)` by metis_tac [list_nchotomy])
        >- FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT,CONS_11]
        >- (FULL_SIMP_TAC list_ss [CONS_11]
          >> first_assum (qspecl_then [`c`,`h'`] strip_assume_tac)
            >> metis_tac [MEM]))));
 

val Logical_to_Functional_Count_Dec_Aux = Q.store_thm ("Logical_to_Functional_Count_Dec_Aux",
 `!t nt p np ba h l.
       (!c. MEM c l ==>
               ((MEM c h ==>
                   (get_cand_pile c np = (get_cand_pile c p)
                     ++ [(FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)])
                /\ (get_cand_tally c nt = (get_cand_tally c t) + (SUM_RAT (
                   (FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba))))))
                            /\ (~ MEM c h ==>
                                           (get_cand_pile c np = get_cand_pile c p)
                                        /\ (get_cand_tally c nt = get_cand_tally c t)))
                                           ==> COUNTAux_dec p np t nt ba h l`,

Induct_on `l`
  >- rw[COUNTAux_dec_def]
  >- ((REPEAT STRIP_TAC
      >> rw[COUNTAux_dec_def])

    >- (first_assum (qspecl_then [`h`] strip_assume_tac)
     >> FULL_SIMP_TAC list_ss [MEM]
      >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
         >> metis_tac [])
    >- (first_assum (qspecl_then [`h`] strip_assume_tac)
     >> FULL_SIMP_TAC list_ss []
       >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
         >> metis_tac [])));
 

val Functional_to_Logical_Count_Dec_Aux = Q.store_thm ("Functional_to_Logical_Count_Dec_Aux",
`!t t' p np ba h l. COUNTAux_dec p np t t' ba h l ==>
          (!c. MEM c l ==>
                 ((MEM c h ==>
                    ?(l': ((cand list) # rat) list).
                      (l' = FILTER (\ (b: (cand list) # rat). (first_continuing_cand c (FST b) h)) ba)
                         /\ (get_cand_pile c np = (get_cand_pile c p) ++ [l'])
                         /\ (get_cand_tally c t' = (get_cand_tally c t) + (SUM_RAT ( l'))))
                         /\ (~ MEM c h ==>
                                      (get_cand_pile c np = get_cand_pile c p)
                                      /\ (get_cand_tally c t' = get_cand_tally c t))))`,

Induct_on `l`
    >- rw[]
    >- (REPEAT STRIP_TAC
      >- ((MAP_EVERY qexists_tac
      [`FILTER (\ (b: (cand list) # rat). (first_continuing_cand_dec c (FST b) h')) ba`]
        >> `!c h ba. first_continuing_cand c h ba <=> first_continuing_cand_dec c h ba`
              by metis_tac [first_continuing_cand_IMP_fcc,fcc_to_first_continuing_cand]
        >> `(c = h) \/ MEM c l` by FULL_SIMP_TAC list_ss [])
            >- (REPEAT STRIP_TAC
               >- metis_tac[]
               >-  metis_tac[COUNTAux_dec_def]
               >-  metis_tac[COUNTAux_dec_def])
            >- (REPEAT STRIP_TAC
              >- metis_tac []
              >- (first_assum (qspecl_then [`t`,`t'`,`p`,`np`,`ba`,`h'`] strip_assume_tac)
                >> `COUNTAux_dec p np t t' ba h' l` by metis_tac[COUNTAux_dec_def]
                >>  FULL_SIMP_TAC list_ss [])
              >- (first_assum (qspecl_then [`t`,`t'`,`p`,`np`,`ba`,`h'`] strip_assume_tac)
                >> `COUNTAux_dec p np t t' ba h' l` by metis_tac[COUNTAux_dec_def]
                >> FULL_SIMP_TAC list_ss [])))
       >- (`(c = h) \/ MEM c l` by FULL_SIMP_TAC list_ss []
         >- metis_tac[COUNTAux_dec_def]
         >- metis_tac[COUNTAux_dec_def])
       >- (`(c = h) \/ MEM c l` by FULL_SIMP_TAC list_ss [MEM]
         >- metis_tac[COUNTAux_dec_def]
         >- metis_tac[COUNTAux_dec_def])));
  

val APPEND_EQ_NIL2 = Q.store_thm ("APPEND_EQ_NIL2",
    `!l1 l2. ([] = l1 ++ l2) ==> ((l1 = []) /\ (l2 = [])) `,
      Cases_on `l2`
        >- ASM_SIMP_TAC bool_ss [APPEND_NIL]
        >- (Cases_on `l1`
          >> rw[APPEND_NIL_LEFT_COR]
            >> (ASM_SIMP_TAC bool_ss [NOT_NIL_CONS]
              >> STRIP_TAC
                >> rw[NOT_NIL_CONS]))) ;

val take_append_returns_appended = Q.store_thm ("take_append_returns_appended",
 `! l1 l2 l3. (l1 = l2 ++ l3) ==> (l3 = take_append l1 l2)`,

 Induct_on `l1`
  >- FULL_SIMP_TAC list_ss [APPEND_EQ_NIL2,take_append_def]
  >- (Induct_on `l2`
    >- FULL_SIMP_TAC list_ss [APPEND_NIL_LEFT,take_append_def]
    >- (REPEAT STRIP_TAC
     >> rw[take_append_def]
       >> FULL_SIMP_TAC list_ss [CONS_11])));
 
val eqe_list_dec_MEM1 = Q.store_thm ("list_eqe_dec_MEM1",
 `!l0 l1 l2. eqe_list_dec l0 l1 l2 ==> (!c. MEM c l0 \/ MEM c l1 ==> MEM c l2)`,

Induct_on `l0`
  >- fs [eqe_list_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional,list_MEM_dec_thm]
  >- (REPEAT STRIP_TAC
     >- metis_tac [eqe_list_dec_def,MEM]
     >- metis_tac [MEM,eqe_list_dec_def]));
 

val logical_to_functional_eqe_list_dec = Q.store_thm ("logical_to_functional_eqe_list_dec",
`!l0 l1 l2. (ALL_DISTINCT (l0 ++ l1)) /\ (!c. MEM c l0 \/ MEM c l1 ==> MEM c l2) ==> eqe_list_dec l0 l1 l2`,

   Induct_on `l0`
     >- metis_tac [eqe_list_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional,list_MEM_dec_thm]
     >-  ((REPEAT STRIP_TAC
       >> rw[eqe_list_dec_def])
          >- fs [ALL_DISTINCT]
          >- (`!c. MEM c l0 \/ MEM c l1 ==> MEM c l2` by metis_tac[MEM]
	    >> `ALL_DISTINCT (l0 ++ l1)` by fs[ALL_DISTINCT]
              >> metis_tac[ALL_DISTINCT,MEM])));


val eqe_list_dec2_verified = Q.store_thm ("eqe_list_dec2_verified",
 `! l0 l1 l2. eqe_list_dec2 l0 l1 l2 <=> (!c. MEM c l2 ==> MEM c l0 \/ MEM c l1)`,
  Induct_on `l2`
    >-  (EVAL_TAC >> rw[])
    >- (REPEAT STRIP_TAC >> rfs[]
        >> fs[eqe_list_dec2_def]
        >> metis_tac[eqe_list_dec2_def]));
 

val functional_to_logical_BiggerThanQuota = Q.store_thm ("functional_to_logical_BiggerThanQuota",
 `! (qu:rat) l t. bigger_than_quota l t qu /\ ALL_DISTINCT (MAP FST t) ==>
                                     (!c. MEM c l ==> (!r. MEM (c,r) t ==> qu <= r))`,

  Induct_on `l`
    >- rw[]
    >- ((REPEAT STRIP_TAC
      >> FULL_SIMP_TAC list_ss [])
         >- (`get_cand_tally c t = r` by metis_tac [ALL_DISTINCT,EVERY_CAND_HAS_ONE_TALLY]
           >> RW_TAC bool_ss [] >> rfs[bigger_than_quota_def])
         >- (`bigger_than_quota l t qu` by fs[bigger_than_quota_def]
	    >> metis_tac [])));

 
val logical_to_functional_BiggerThanQuota = Q.store_thm ("logical_to_functional_BiggerThanQuota",
`! (qu: rat) l t. (ALL_DISTINCT (MAP FST t)) /\ (!d. MEM d l ==> MEM d (MAP FST t)) /\
                  (!c. MEM c l ==> (!r. MEM (c,r) t ==> qu <= r)) ==> bigger_than_quota l t qu`,

  Induct_on `l`
     >- rw[bigger_than_quota_def]
     >- ((REPEAT STRIP_TAC
       >> rw[bigger_than_quota_def])
          >- (`MEM (h,get_cand_tally h t) t` by metis_tac [MEM,GET_CAND_TALLY_MEM2]
            >> metis_tac[MEM])
          >- metis_tac [bigger_than_quota_def,MEM]));
 
 
val functional_to_logicl_piles_eq = Q.store_thm ("functional_to_logical_piles_eq",
 `! l1 l2 p1 p2. ALL_DISTINCT (MAP FST p1) /\ ALL_DISTINCT (MAP FST p2) /\ (list_MEM_dec l1 (MAP FST p1)) /\
                (list_MEM_dec l1 (MAP FST p2)) /\ (piles_eq_list l1 l2 p1 p2) ==>
   (!c. MEM c l1 ==> (~ MEM c l2 ==> (!l'. MEM (c,l') p1 <=> MEM (c,l') p2)))`,


Induct_on `l1`
 >- rw[]

 >- ((REPEAT STRIP_TAC
    >> Cases_on `c= h`)

  >- (`get_cand_pile h p1 = get_cand_pile h p2` by metis_tac [piles_eq_list_def] >>
     (`MEM (h,l') p1 ==> MEM (h, l') p2` by (STRIP_TAC >>
     `get_cand_pile c p1 = l'` by
     metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
     GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
       `MEM (h,get_cand_pile h p2) p2` by
       metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
       GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
         `l' = get_cand_pile h p2` by
         metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
         GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
           metis_tac [MEM])) >>
     (`MEM (h,l') p2 ==> MEM (h,l') p1` by (STRIP_TAC >>
     `get_cand_pile c p2 = l'`
     by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
     GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
       `MEM (h,get_cand_pile h p1) p1` by
       metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
       GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
         `l' = get_cand_pile h p1` by
         metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,
         GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE] >>
            metis_tac [MEM])) >>
     metis_tac [MEM])
  >- (`list_MEM_dec l1 (MAP FST p1)` by metis_tac [MEM,Logical_list_MEM_VICE_VERCA_TheFunctional] >>
      `list_MEM_dec l1 (MAP FST p2)` by metis_tac [MEM,Logical_list_MEM_VICE_VERCA_TheFunctional] >>
      `piles_eq_list l1 l2 p1 p2` by metis_tac [piles_eq_list_def] >>
      metis_tac [MEM])));
 
 
val logical_to_functional_piles_eq = Q.store_thm ("logical_to_functional_piles_eq",
`! l1 l2 p1 p2.  (!c. MEM c l1 ==> (~ MEM c l2 ==> (!l'. MEM (c,l') p1 <=> MEM (c,l') p2)))
              /\ (ALL_DISTINCT (MAP FST p1)) /\ (ALL_DISTINCT (MAP FST p2) )
              /\ (!d. MEM d l1 ==> MEM d (MAP FST p1) /\ MEM d (MAP FST p2)) ==> piles_eq_list l1 l2 p1 p2`,

  Induct_on `l1`
    >- rw[piles_eq_list_def]
    >- (REPEAT STRIP_TAC
     >> rw[piles_eq_list_def]
      >> `!l'. MEM (h,l') p1 <=> MEM (h,l') p2` by FULL_SIMP_TAC list_ss [MEM]
       >> metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE,MEM]));
 

val functional_to_logical_update_pile = Q.store_thm ("functional_to_logical_update_pile",
 `! (qu: rat) (t: (cand # rat) list) l p1 p2. (ALL_DISTINCT (MAP FST p1)) /\ (ALL_DISTINCT (MAP FST p2))
        /\   (update_cand_pile qu t l p1 p2) ==>
              (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                         (MAP FST (FLAT l') = MAP FST (FLAT(get_cand_pile c p1)))
                                      /\ (MAP SND (FLAT l') = update_cand_trans_val qu c t (FLAT (get_cand_pile c p1)))))`,

   Induct_on `l`
     >- rw[]
     >- (REPEAT STRIP_TAC
       >- (FULL_SIMP_TAC list_ss []
          >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
           >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
            >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
             >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
              >> metis_tac [update_cand_pile_def])
          >- metis_tac [update_cand_pile_def])
       >- (FULL_SIMP_TAC list_ss []
         >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
          >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
           >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
            >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
             >> metis_tac[update_cand_pile_def])
       >- metis_tac [update_cand_pile_def])));
  
 
val logical_to_functional_update_pile = Q.store_thm ("logical_to_functional_update_pile",
 `! (qu: rat) (t: (cand #rat) list) l p1 p2. (!c. MEM c l ==> MEM c (MAP FST p2)) /\
                                            (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                              (MAP FST (FLAT l') = MAP FST (FLAT (get_cand_pile c p1)))
                                                /\ (MAP SND (FLAT l') = update_cand_trans_val qu c t (FLAT (get_cand_pile c p1))))) ==>
                                                    (update_cand_pile qu t l p1 p2)`,

    Induct_on `l`
      >- rw [update_cand_pile_def]
      >- ((REPEAT STRIP_TAC
       >> rw[update_cand_pile_def])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])));
  

val tally_comparison_total = Q.store_thm ("tally_comparison_total",
 `!t c1 c2. ((tally_comparison t) c1 c2) \/ ((tally_comparison t) c2 c1)`,
  ((REPEAT STRIP_TAC
    >> rw[tally_comparison_def]
     >> ASSUME_TAC RAT_LES_TOTAL
      >> first_assum (qspecl_then [`get_cand_tally c2 t`,`get_cand_tally c1 t`] strip_assume_tac))
         >- (DISJ1_TAC
          >> metis_tac [RAT_LES_IMP_LEQ])
         >- (DISJ1_TAC
          >> metis_tac [RAT_LEQ_REF])
         >- (DISJ2_TAC
          >> metis_tac [RAT_LES_IMP_LEQ])));

 
val tally_comparison_total_COR = Q.store_thm ("tally_comparison_total_COR",
 `!t. total (tally_comparison t)`,

   (ASSUME_TAC (INST_TYPE [alpha |-> ``:cand``] total_def)
     >> STRIP_TAC
       >> first_assum (qspecl_then [`tally_comparison t`] strip_assume_tac)
         >> metis_tac [tally_comparison_total]));

 

val tally_comparison_trans = Q.store_thm ("tally_comparison_trans",
 `!t. transitive (tally_comparison t)`,

   (STRIP_TAC
     >> `! c1 c2 c3. (tally_comparison t) c1 c2 /\ (tally_comparison t) c2 c3 ==> (tally_comparison t) c1 c3`
       by (REPEAT STRIP_TAC
        >> metis_tac [tally_comparison_def,RAT_LEQ_TRANS])
          >> metis_tac[transitive_def]));
 
 
val subpile1_BlMem_trans2_IsCorrect = Q.store_thm ("subpile1_BlMem_trans2_IsCorrect",
 `!p bl. (!d. MEM d bl ==> MEM (d,[]) p) <=> subpile1_BlMem_trans2 p bl`,

  Induct_on `bl`
    >- rw[subpile1_BlMem_trans2_def]   
    >- (REPEAT STRIP_TAC >> fs[MEM,subpile1_BlMem_trans2_def] >> metis_tac[]));
   
 
val Logical_to_Functional_subpileBacklogTrans2 = Q.store_thm("Logical_to_Functional_subpileBacklogTrans2",
  `!bl p np. (!d'. (~ MEM d' bl ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np)))
                /\ (MEM d' bl ==> MEM (d',[]) np)) ==> (subpile1_backlog_trans2 bl p np)`,
 
   Induct_on `p` 
       >- rw[subpile1_backlog_trans2_def]
       >-((REPEAT STRIP_TAC  
        >> rw[subpile1_backlog_trans2_def]
        >> (` !d'. (¬MEM d' bl ⇒ ∀l'. MEM (d',l') p ⇒ MEM (d',l') np)` by fs[]) 
        >>  (`!d'. MEM d' bl ⇒ MEM (d',[]) np` by fs[])
        >> rw[subpile1_backlog_trans2_def])   
         >- (first_assum(qspecl_then [`bl`,`np`] strip_assume_tac)
          >> (`subpile1_backlog_trans2 bl p np` by fs[])
           >> rfs[subpile1_backlog_trans2_def])
         >- ((`∀l'. MEM (FST h,l') (h::p) ⇒ MEM (FST h,l') np` by metis_tac[]) 
          >> first_assum(qspecl_then [`SND h`] strip_assume_tac)
           >> (`(FST h, SND h) = h` by rfs[PAIR])      
            >> (`MEM (FST h, SND h) (h::np)` by fs[])
          >> fs[])  
         >- (first_assum(qspecl_then [`bl`,`np`] strip_assume_tac)
          >> (`subpile1_backlog_trans2 bl p np` by fs[])
           >> rfs[subpile1_backlog_trans2_def])));
         
val Functional_to_Logical_subpile1BacklogTrans2 = Q.store_thm("Functional_to_Logical_subpile1BacklogTrans2",
 `!bl p np. subpile1_backlog_trans2 bl p np ==> (!d'. (~ MEM d' bl ==> (!l'. (MEM (d',l') p ==> MEM (d',l') np))))`,

 Induct_on`p`
   >- rw[]
   >- ((REPEAT STRIP_TAC
     >> Cases_on`d' = FST h`)
    >- (fs[subpile1_backlog_trans2_def]
      >> first_assum(qspecl_then [`bl`,`np`] strip_assume_tac)
       >> fs[])
     >- (fs[subpile1_backlog_trans2_def]
      >- (rw[] >> fs[FST]) 
      >- (first_assum(qspecl_then[`bl`,`np`] strip_assume_tac)
           >> fs[])))); 
  
val Functional_to_Logical_subpile2_backlog_trans2 = Q.store_thm("Functional_to_Logical_subpile2_backlog_trans2",
 `!bl p np. subpile2_backlog_trans2 bl np p ==>  (!d'. (~ MEM d' bl ==> (!l'. (MEM (d',l') np ==> MEM (d',l') p))))`,

  Induct_on`np`
    >- rw[]
    >- ((REPEAT STRIP_TAC 
     >>  first_assum(qspecl_then [`bl`,`p`] strip_assume_tac)
      >> `subpile2_backlog_trans2 bl np p` by fs[subpile2_backlog_trans2_def]
       >> Cases_on`d' = FST h`)
        >- fs[subpile2_backlog_trans2_def]
        >- (`MEM (d',l') np` by (FULL_SIMP_TAC list_ss [MEM] >> rw[] >> rfs[FST]) 
         >> fs[])));       
   
    
val Logical_to_Functional_subpile2Backlog_trans = Q.store_thm("Logical_to_Functional_subpile2Backlog_trans",
  `!bl p np. (!d'. (~ MEM d' bl ==> (!l'. (MEM (d',l') np ==> MEM (d',l') p)))
           ) ==>
           subpile2_backlog_trans2 bl np p`,
   
Induct_on`np`
   >- rw[subpile2_backlog_trans2_def]  
   >- ((REPEAT STRIP_TAC 
     >> rw[subpile2_backlog_trans2_def])   
      >- (Cases_on`MEM (FST h) bl`  
          >- fs[]  
          >- (first_assum(qspecl_then [`FST h`] strip_assume_tac)  
            >> ` ∀l'. MEM (FST h,l') (h::np) ⇒ MEM (FST h,l') p` by (rfs[] >> fs[]) 
	     >> first_assum(qspecl_then[`SND h`] strip_assume_tac) 
              >> fs[]))
      >- (first_assum(qspecl_then [`bl`,`p`] strip_assume_tac)
        >> rfs[subpile2_backlog_trans2_def])));
  
 
val Functional_AllNonZero_to_Logical = Q.store_thm("Functional_AllNonZero_to_Logical",
 `! l p. ALL_NON_ZERO p l ==> (!c. MEM c l ==> SUM_RAT (LAST (get_cand_pile c p)) <> 0)`,

Induct
  >- rw[]
  >- (rw[]
      >- rfs[ALL_NON_ZERO_def,MEM]
      >- rfs[ALL_NON_ZERO_def,MEM]));
 

val Logical_AllNonZero_to_Functional = Q.store_thm("Logical_AllNonZero_to_Functional",
 `!l p . (!c. MEM c l ==> SUM_RAT (LAST (get_cand_pile c p)) <> 0) ==> ALL_NON_ZERO p l`,

Induct
   >- rw[ALL_NON_ZERO_def]
   >- rfs[ALL_NON_ZERO_def,MEM]);
 
val Logical_AllNonEpty_to_Functional = Q.store_thm("Logical_AllNonEpty_to_Functional",
 `! l p. (ALL_DISTINCT (MAP FST p)) /\ (!c. MEM c l ==> MEM c (MAP FST p)) ==>
         (!c. MEM c l ==> (!l'. MEM (c,l') p ==> l' <> [])) ==> ALL_NON_EMPTY p l`,

Induct_on`l`
   >- rw[ALL_NON_EMPTY_def] 
   >- (rw[ALL_NON_EMPTY_def]
       >- metis_tac[GET_CAND_PILE_MEM,MEM,ALL_NON_EMPTY_def]
       >- metis_tac[ALL_NON_EMPTY_def,MEM]));
 

val Functional_AllNonEmpty_to_Logical = Q.store_thm("Functional_AllNonEmpty_to_Logical",
 `!l p. (ALL_DISTINCT (MAP FST p)) /\ (!c. MEM c l ==> MEM c (MAP FST p)) ==>
         (ALL_NON_EMPTY p l) ==> (!c. MEM c l ==> (!l'. MEM (c,l') p ==> l' <> []))`,

Induct_on `l`
    >- rw[]
    >- (rw[]
     >- (rfs[ALL_NON_EMPTY_def]
         >> metis_tac[ALL_NON_EMPTY_def,EVERY_CAND_HAS_ONE_PILE,MEM])
     >- rfs[ALL_NON_EMPTY_def]));
 
 
val functional_to_logical_update_pile_ACT = Q.store_thm ("functional_to_logical_update_pile_ACT",
 `! (qu: rat) (t: (cand # rat) list) l p1 p2. (ALL_DISTINCT (MAP FST p1)) /\ (ALL_DISTINCT (MAP FST p2))
        /\   (update_cand_pile_ACT qu t l p1 p2) ==>
              (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                         (MAP FST (LAST l') = MAP FST (LAST (get_cand_pile c p1)))
                                      /\ (MAP SND (LAST l') = update_cand_transVal_ACT qu c t p1)))`,

   Induct_on `l`
     >- rw[]
     >- (REPEAT STRIP_TAC
       >- (FULL_SIMP_TAC list_ss []
          >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
           >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
            >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
             >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
              >> metis_tac [update_cand_pile_ACT_def])
          >- metis_tac [update_cand_pile_ACT_def])
       >- (FULL_SIMP_TAC list_ss []
         >- (`? l1 l2. p2 = l1 ++ (c,l') ::l2` by metis_tac [MEM,MEM_SPLIT]
          >> `MAP FST p2 = (MAP FST l1) ++ c :: (MAP FST l2)` by FULL_SIMP_TAC list_ss [FST,MAP_APPEND_TRIO]
           >> `MEM c (MAP FST p2)` by FULL_SIMP_TAC list_ss [MEM_APPEND]
            >> `l' = get_cand_pile h p2` by metis_tac [GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE]
             >> metis_tac[update_cand_pile_ACT_def])
       >- metis_tac [update_cand_pile_ACT_def])));


val logical_to_functional_update_pile_ACT = Q.store_thm ("logical_to_functional_update_pile_ACT",
 `! (qu: rat) (t: (cand #rat) list) l p1 p2. (!c. MEM c l ==> MEM c (MAP FST p2)) /\
                                            (!c. MEM c l ==> (!l'. MEM (c,l') p2 ==>
                                              (MAP FST (LAST l') = MAP FST (LAST (get_cand_pile c p1)))
                                                /\ (MAP SND (LAST l') = update_cand_transVal_ACT qu c t p1))) ==>
                                                    (update_cand_pile_ACT qu t l p1 p2)`,

    Induct_on `l`
      >- rw [update_cand_pile_ACT_def]
      >- ((REPEAT STRIP_TAC
       >> rw[update_cand_pile_ACT_def])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])
          >- (`MEM (h,get_cand_pile h p2) p2` by metis_tac [MEM,GET_CAND_PILE_MEM]
            >> metis_tac [MEM])));
 

val _ = export_theory();
