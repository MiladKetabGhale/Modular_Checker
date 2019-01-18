open preamble
     AuxSpecTheory
     AuxIMPTheory
     AuxEquivProofsTheory 
     AuxRulesSpecTheory
     AuxRulesIMPTheory
     ratTheory
                                   
  
val _ = new_theory "AuxRulesEquivProofs"
       
val Logical_ElimAux_to_Functional = Q.store_thm ("Logical_ElimAux_to_Functional",
 `!st qu l c t p np bl2 nbl2 e h nh.
        ELIM_CAND_Auxiliary c (qu,st,l) t p np bl2 nbl2 e h nh ==> (ELIM_CAND_Auxiliary_dec c (qu,st,l) t p np  bl2 nbl2 e h nh)`,
 
   REPEAT STRIP_TAC >> fs[ELIM_CAND_Auxiliary_def,ELIM_CAND_Auxiliary_dec_def]  
		>> `MEM c (MAP FST p)` by metis_tac [Valid_PileTally_def,FST,MAP] 
                >> `!d. MEM d h ==> MEM d (MAP FST p)` by metis_tac [Valid_PileTally_def]  
                >> fs [Valid_Init_CandList_def,NULL,NULL_EQ,
	               PileTally_to_PileTally_DEC2,PileTally_to_PileTally_DEC1,
		       Valid_PileTally_def,EQE_IMP_REMOVE_ONE_CAND,
		       LogicalLessThanQu_IMP_less_than_quota,Valid_PileTally_def,ALOOKUP_def,
		       Logical_bigger_than_cand_IMP_TheFunctional]
		>> `!(l1:cand list) l2 (c':cand). MEM c' l1 \/ MEM c' l2 ==> MEM c' (l1++l2)`
                     by FULL_SIMP_TAC list_ss [MEM,MEM_APPEND]  
                >> metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,MEM]);    
   

(* the old proof when bl2 was captured to have more than one cand in it 
               >- (`!c'. MEM c' (h++e) ==> MEM c' l` by metis_tac [MEM,MEM_APPEND]  
		>> `MEM c (MAP FST p)` by metis_tac [Valid_PileTally_def,FST,MAP] 
                >> `!d. MEM d h ==> MEM d (MAP FST p)` by metis_tac [Valid_PileTally_def]  
                >> fs [Valid_Init_CandList_def,NULL,NULL_EQ,
	               PileTally_to_PileTally_DEC2,PileTally_to_PileTally_DEC1,
		       Valid_PileTally_def,EQE_IMP_REMOVE_ONE_CAND,
		       LogicalLessThanQu_IMP_less_than_quota,Valid_PileTally_def,ALOOKUP_def,
		       Logical_bigger_than_cand_IMP_TheFunctional]
		>> `!(l1:cand list) l2 (c':cand). MEM c' l1 \/ MEM c' l2 ==> MEM c' (l1++l2)`
                     by FULL_SIMP_TAC list_ss [MEM,MEM_APPEND]  
                >> metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,MEM]));    
*)
  
val Functional_ElimAux_to_Logical = Q.store_thm ("Functional_ElimAux_to_Logical",
 `!st qu l c t p np bl2 nbl2 e h nh.
     ELIM_CAND_Auxiliary_dec c (qu,st,l) t p np bl2 nbl2 e h nh ==> ELIM_CAND_Auxiliary c (qu,st,l) t p np bl2 nbl2 e h nh`,
           
    (REPEAT STRIP_TAC  
	>> rfs[ELIM_CAND_Auxiliary_def,ELIM_CAND_Auxiliary_dec_def]             
         >> fs [NULL,NULL_EQ,Logical_list_MEM_VICE_VERCA_TheFunctional,
	       MEM,Valid_Init_CandList_def,EQE_REMOVE_ONE_CAND,ALL_DISTINCT_APPEND,
	       Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
	       PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota,
	       PileTally_to_PileTally_DEC2,bigger_than_cand_LogicallyOK,
	       MEM,Valid_Init_CandList_def,EQE_REMOVE_ONE_CAND,ALL_DISTINCT_APPEND]
           >> REPEAT CONJ_TAC) 
           >- (`!d'. MEM d' (h++e) ==> MEM d' l` by FULL_SIMP_TAC list_ss [MEM,MEM_APPEND,list_MEM_dec_def,
	                                             Logical_list_MEM_VICE_VERCA_TheFunctional]   
             >> metis_tac[MEM_APPEND,MEM]) 	  
             >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
             >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
             >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
             >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]   
                      >> `MEM y (MAP FST t)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM] 
                      >> `?l1 q1. t = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy] 
                      >> `!d. MEM d h ==> MEM d l`
                           by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]  
                      >> `!d. MEM d h ==> MEM d (MAP FST t)` by metis_tac [PileTally_DEC2_IMP_PileTally] 
                    >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota])    
             >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                     >> `MEM y (MAP FST t)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. t = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d h ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                     >> `!d. MEM d h ==> MEM d (MAP FST t)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac [PileTally_to_PileTally_DEC2,bigger_than_cand_LogicallyOK]));
 		     
        
val Logical_TransferAux_to_Functional = Q.store_thm ("Logical_TransferAux_to_Functional",
 `! st qu l ba t t' p np bl bl2 bl2' e e' h h'. TRANSFER_Auxiliary (qu,st,l) ba t t' p np bl bl2 bl2' e e' h h'
             ==> TRANSFER_Auxiliary_dec (qu,st,l) ba t t' p np bl bl2 bl2' e e' h h'`,
   
  REPEAT STRIP_TAC
   >> fs[TRANSFER_Auxiliary_def,TRANSFER_Auxiliary_dec_def]
     >> (STRIP_TAC              
        >- (`(!d. MEM d h \/ MEM d e ==> MEM d l) ==> (!d. MEM d (h++e) ==> MEM d l)`
               by  FULL_SIMP_TAC list_ss [MEM_APPEND] >>  
               metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])     
        >- (fs[Logical_list_MEM_VICE_VERCA_TheFunctional]  
	    >> fs[PileTally_to_PileTally_DEC1,Valid_PileTally_def,
	       PileTally_to_PileTally_DEC2,NULL_EQ,NULL,
	       Valid_Init_CandList_def,LogicalLessThanQu_IMP_less_than_quota,MEM])));
         
     
val Functional_TransferAux_to_Logical = Q.store_thm("Functional_TransferAux_to_Logical",
 `! st qu l ba t t' p np bl bl2 bl2' e e' h h'. TRANSFER_Auxiliary_dec (qu,st,l) ba t t' p np bl bl2 bl2' e e' h h'
                   ==> TRANSFER_Auxiliary (qu,st,l) ba t t' p np bl bl2 bl2' e e' h h'`,
    
 (REPEAT STRIP_TAC >> 
  fs[TRANSFER_Auxiliary_dec_def,TRANSFER_Auxiliary_def]
   >> fs[NULL,NULL_EQ,Valid_Init_CandList_def,NULL_EQ,MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional,
        Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
	less_than_qu_IMP_LogicalLessThanQuota]   
   >> REPEAT CONJ_TAC)                   
    >- metis_tac[MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional] 
    >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
    >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
    >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
    >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                     >> `MEM y (MAP FST t)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. t = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d h ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
		     >> `!d. MEM d h ==> MEM d (MAP FST t)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota]));  
      

val Logical_CountAux_to_Functional = Q.store_thm ("Logical_CountAux_to_Functional",
 `! (st: num) (qu: rat) l ba nba t nt p np e h.
   COUNT_Auxiliary (qu,st,l) ba nba t nt p np e h ==> COUNT_Auxiliary_dec (qu,st,l) ba nba t nt p np e h`,

      REPEAT STRIP_TAC
       >> fs[COUNT_Auxiliary_def,COUNT_Auxiliary_dec_def] 
          >> metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,Valid_PileTally_def,
	    PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,Valid_Init_CandList_def,NULL_EQ,NULL]); 

val Functional_COUNTAux_to_Logical = Q.store_thm("Functional_COUNTAux_to_Logical",
 `! (st: num) (qu: rat) l ba nba t nt p np e h.
  COUNT_Auxiliary_dec (qu,st,l) ba nba t nt p np e h ==> COUNT_Auxiliary (qu,st,l) ba nba t nt p np e h`,

  REPEAT STRIP_TAC
   >> fs[COUNT_Auxiliary_dec_def, COUNT_Auxiliary_def]
     >> metis_tac[list_MEM_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,
		  Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
	          Valid_Init_CandList_def,NULL_EQ,NULL,Valid_PileTally_def,
	          PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]);	   		      
    
val TAKE_DROP_LENGTH_BACKLOG = Q.store_thm ("TAKE_DROP_LENGTH_BACKLOG",
 `! bl nbl (l1: cand list). nbl = bl ++ l1 ==> (bl = TAKE (LENGTH bl) nbl) /\ (l1 = DROP (LENGTH bl) nbl)`, 
  
  REPEAT STRIP_TAC   
   >- FULL_SIMP_TAC list_ss [TAKE_APPEND1,APPEND_11]    
   >- (`TAKE (LENGTH bl) nbl = bl` by FULL_SIMP_TAC list_ss [TAKE_APPEND1,TAKE_LENGTH_ID]   
        >> `nbl = (TAKE (LENGTH bl) nbl) ++ (DROP (LENGTH bl) nbl)` by  FULL_SIMP_TAC list_ss [TAKE_DROP]
          >> metis_tac[APPEND_11]));  

 
val DROP_LENGTH = Q.store_thm ("DROP_LENGTH",
 `! bl (l1: cand list). DROP (LENGTH bl) (bl ++ l1) = l1`,
 Induct_on `bl`
   >- rw[]
   >- (REPEAT STRIP_TAC 
     >> FULL_SIMP_TAC list_ss [DROP,MEM]));
     
val Logical_ElectAux_to_Functional = Q.store_thm ("Logical_ElectAux_to_Functional",
 `! st (qu: rat) l ba t p np bl nbl e ne h nh l1. ELECT_Auxiliary (qu,st,l) ba t p np bl nbl e ne h nh l1
        ==> ELECT_Auxiliary_dec (qu,st,l) ba t p np bl nbl e ne h nh l1`,
  
   (REPEAT STRIP_TAC
    >> fs[ELECT_Auxiliary_def, ELECT_Auxiliary_dec_def]
     >> `DROP (LENGTH bl) (bl ++ l1) = l1` by metis_tac[TAKE_DROP_LENGTH_BACKLOG]
      >> fs[NULL,NULL_EQ]
       >> `(!c. MEM c l ==> MEM c (MAP FST p))` by metis_tac [MEM,Valid_PileTally_def]
	 >> `(!c. MEM c h ==> MEM c (MAP FST np))` by metis_tac [MEM,Valid_PileTally_def] 
 	 >> `!c. MEM c l1 ==> MEM c (MAP FST t)` by metis_tac [MEM, Valid_PileTally_def] 
         >> fs [logical_to_functional_eqe_list_dec,logical_to_functional_piles_eq,
                   eqe_list_dec2_verified,TAKE_DROP_LENGTH_BACKLOG,Valid_Init_CandList_def,
	           Logical_list_MEM_VICE_VERCA_TheFunctional]
          >> REPEAT CONJ_TAC) 
           
 	    >- (`!c. MEM c l1 ==> MEM c (MAP FST t)`
	         by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM, Valid_PileTally_def]  
             >> metis_tac [logical_to_functional_BiggerThanQuota,bigger_than_quota_def,MEM])
	    >- metis_tac [logical_to_functional_eqe_list_dec]
	    >- metis_tac [logical_to_functional_piles_eq,logical_to_functional_eqe_list_dec,
	                   eqe_list_dec2_verified] 
	    >- metis_tac [logical_to_functional_eqe_list_dec] 
	    >- metis_tac[]     
            >- (`(!c. MEM c h ==> MEM c (MAP FST p) /\ MEM c (MAP FST np))`
	         by metis_tac [MEM,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional]
	     >> metis_tac [logical_to_functional_piles_eq])
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2] 
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
            >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
	    >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]);
        
    
val Functional_ElectAux_to_Logical = Q.store_thm ("Functional_ElectAux_to_Logical",
 `! st qu l ba t p np bl nbl e ne h nh l1. ELECT_Auxiliary_dec (qu,st,l) ba t p np bl nbl e ne h nh l1 
                     ==> ELECT_Auxiliary (qu,st,l) ba t p np bl nbl e ne h nh l1`,

 ((REPEAT STRIP_TAC
  >> fs[ELECT_Auxiliary_dec_def,ELECT_Auxiliary_def]
   
   >> fs[NULL,NULL_EQ,MEM]   
         >> REPEAT CONJ_TAC)
	 >- rfs[]         
       >- metis_tac [functional_to_logical_BiggerThanQuota]
        >- rfs[LENGTH_DROP]   
       >- metis_tac [list_eqe_dec_MEM1,MEM]  
       >- metis_tac [eqe_list_dec2_verified,MEM]  
       >- metis_tac [list_eqe_dec_MEM1,MEM] 
       >- metis_tac [eqe_list_dec2_verified]  
       >- (rw[] >> `!c. MEM c h ==> MEM c l` by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional]
         >> `!c. MEM c h ==> MEM c (MAP FST np)`
           by metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,MEM]
          >> `!c. MEM c h ==> MEM c (MAP FST p)`
              by metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
                    MEM,Logical_list_MEM_VICE_VERCA_TheFunctional]
          >> metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,functional_to_logical_piles_eq]) 
       >- metis_tac[TAKE_DROP] 
       >- metis_tac [Valid_Init_CandList_def,NULL_EQ] 
       >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
       >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
       >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
       >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional]
       >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])); 
  
 
val Logical_TransferExcludedAux_to_Functional = Q.store_thm("Logical_TransferExcludedAux_to_Functional",
 `! qu st l j1 j2. TRANSFER_EXCLUDED_Auxiliary (qu,st,l) j1 j2
                                        ==> TRANSFER_EXCLUDED_Auxiliary_dec (qu,st,l) j1 j2`, 
  
 (REPEAT STRIP_TAC
  >> fs[TRANSFER_EXCLUDED_Auxiliary_def,TRANSFER_EXCLUDED_Auxiliary_dec_def]
   >> REPEAT CONJ_TAC)              
    >- (Cases_on `MEM (c, []) p'`       
       >- (`get_cand_pile c p' = []` by metis_tac[EVERY_CAND_HAS_ONE_PILE,Valid_PileTally_def]
        >> fs[NULL,NULL_EQ])  
       >- (fs[MEM,NULL,NULL_EQ] >> strip_tac
          >> `get_cand_pile c p' = []` by metis_tac[EVERY_CAND_HAS_ONE_PILE,Valid_PileTally_def]
           >> `MEM c (MAP FST p')` by metis_tac[MEM,MAP,MEM_MAP,FST]
             >> metis_tac[GET_CAND_PILE_MEM,MEM,Valid_Init_CandList_def,Valid_PileTally_def]))    
       >- (`! l1 (l2: cand list). (!d. MEM d l1 \/ MEM d l2 <=> MEM d (l1 ++ l2))` 
                by  metis_tac[MEM,MEM_APPEND]
	      >> first_assum(qspecl_then [`h`,`e`] strip_assume_tac)  
               >> metis_tac[list_MEM_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional])
    >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
    >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
    >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
    >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
    >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
    >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
    >- fs[NULL,NULL_EQ,Valid_Init_CandList_def]  
    >- fs[Valid_Init_CandList_def]   
    >- (`!d. MEM d h' ==> MEM d l`
           by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
      >> `!d. MEM d h' ==> MEM d (MAP FST t')` by 
 	   metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,
		      PileTally_DEC2_IMP_PileTally,Valid_Init_CandList_def,
		      Valid_PileTally_def,PileTally_to_PileTally_DEC1,
     		     PileTally_to_PileTally_DEC2]
        >> metis_tac [PileTally_to_PileTally_DEC2,LogicalLessThanQu_IMP_less_than_quota])     
    >- (Cases_on `ReGroup_Piles (QSORT3 (λx y. SND x ≤ SND y) (FLAT (get_cand_pile c p)))`
          >- fs[]
          >- simp[]) 
    >- metis_tac[MEM,Logical_to_Functional_subpile2Backlog_trans]          
    >- metis_tac[MEM,Logical_to_Functional_subpile2Backlog_trans]);        
      
 
            
val Functional_TransferExcluded_Aux_to_Logical = Q.store_thm("Functional_TransferExcluded_Aux_to_Logical",
 `! qu st l j1 j2. TRANSFER_EXCLUDED_Auxiliary_dec (qu,st,l) j1 j2
                                        ==> TRANSFER_EXCLUDED_Auxiliary (qu,st,l) j1 j2`,
(REPEAT STRIP_TAC
    >> Cases_on`j1`  
     >- (Cases_on`j2`  
      >- ((PairCases_on`p` >> PairCases_on`p'`   
       >> fs[TRANSFER_EXCLUDED_Auxiliary_dec_def,TRANSFER_EXCLUDED_Auxiliary_def]  
        >> Cases_on `p4`) 
	>- rfs[]  
	>- ((fs[] >> REPEAT CONJ_TAC)       
          >- fs[NULL,NULL_EQ]   
          >- metis_tac[NULL,NULL_EQ,GET_CAND_PILE_MEM,MEM,Valid_Init_CandList_def,Valid_PileTally_def,
     	                    EVERY_CAND_HAS_ONE_PILE] 
          >- (Cases_on`ReGroup_Piles 
             (QSORT3 (λx y. SND x ≤ SND y) (FLAT (get_cand_pile h p2)))`
                 >- fs[]
                 >- (fs[] >> 
                  metis_tac [MEM,NULL,NULL_EQ,GET_CAND_PILE_MEM,MEM,
			  Valid_Init_CandList_def,Valid_PileTally_def,EVERY_CAND_HAS_ONE_PILE,
		 	   PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]))
          >- (`! l1 (l2: cand list). (!d. MEM d l1 \/ MEM d l2 <=> MEM d (l1 ++ l2))` 
                by  metis_tac[MEM,MEM_APPEND]
	      >> first_assum(qspecl_then [`p5`,`p6`] strip_assume_tac)  
               >> metis_tac[list_MEM_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional])
          >- metis_tac[list_MEM_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional,MEM,MEM_APPEND] 
          >- rfs[]  
          >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
          >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
          >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
          >- fs[Valid_Init_CandList_def,NULL,NULL_EQ]
	  >- rfs[]  
          >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]   
                      >> `MEM y (MAP FST p1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM] 
                      >> `?l1 q1. p1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy] 
                      >> `!d. MEM d p6 ==> MEM d l`
                           by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]  
                      >> `!d. MEM d p6 ==> MEM d (MAP FST p1)` by metis_tac [PileTally_DEC2_IMP_PileTally] 
                    >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota])    
          >- metis_tac[Functional_to_Logical_subpile2_backlog_trans2,MEM]
	  >- (Cases_on` ReGroup_Piles
             (QSORT3 (λx y. SND x ≤ SND y) (FLAT (get_cand_pile h p2)))` 
	       >- rfs[] 
	       >- rfs[]) 
	  >- (Cases_on` ReGroup_Piles
             (QSORT3 (λx y. SND x ≤ SND y) (FLAT (get_cand_pile h p2)))`  
	       >- rfs[]  
	       >- rfs[])
	  >- (Cases_on` ReGroup_Piles
             (QSORT3 (λx y. SND x ≤ SND y) (FLAT (get_cand_pile h p2)))` 
	       >- rfs[] 
	       >- rfs[])))
	>- rfs[TRANSFER_EXCLUDED_Auxiliary_dec_def])
      >- rfs[TRANSFER_EXCLUDED_Auxiliary_dec_def]));  
           
  

 
(* --------------eliminated parts of proofs for elimination_aux -------- *)
(*

 >- (`!(l1:cand list) l2 (c':cand). MEM c' l1 \/ MEM c' l2 ==> MEM c' (l1++l2)`
                by FULL_SIMP_TAC list_ss [MEM,MEM_APPEND] 
                >> `!c'. MEM c' (p6++p5) ==> MEM c' l` by metis_tac [MEM,MEM_APPEND]  
                 >> metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])  
	      >- (`MEM c (MAP FST p1)` by metis_tac [Valid_PileTally_def,FST,MAP]
               >> `!d. MEM d p6 ==> MEM d (MAP FST p1)` by metis_tac [Valid_PileTally_def]
                >> metis_tac [Logical_bigger_than_cand_IMP_TheFunctional]))  
               
           >- ((fs[Valid_Init_CandList_def,NULL,NULL_EQ,
	        PileTally_to_PileTally_DEC2,PileTally_to_PileTally_DEC1,Valid_PileTally_def,
	        EQE_IMP_REMOVE_ONE_CAND,LogicalLessThanQu_IMP_less_than_quota,
		Valid_PileTally_def,ALOOKUP_def]
             >> REPEAT STRIP_TAC) 
	      >- (`!(l1:cand list) l2 (c':cand). MEM c' l1 \/ MEM c' l2 ==> MEM c' (l1++l2)`
                by FULL_SIMP_TAC list_ss [MEM,MEM_APPEND] 
                >> `!c'. MEM c' (p6++p5) ==> MEM c' l` by metis_tac [MEM,MEM_APPEND]  
                 >> metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])  
	      >- (`MEM c (MAP FST p1)` by metis_tac [Valid_PileTally_def,FST,MAP]  
               >> `!d. MEM d p6 ==> MEM d (MAP FST p1)` by metis_tac [Valid_PileTally_def]
                >> metis_tac [Logical_bigger_than_cand_IMP_TheFunctional]))) 
       >- rfs[ELIM_CAND_Auxiliary_def])
      >- rfs[ELIM_CAND_Auxiliary_def]); 




>- fs [Valid_Init_CandList_def,NULL,NULL_EQ,ALL_DISTINCT,
                 Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,
	         Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
		 EQE_REMOVE_ONE_CAND,ALL_DISTINCT_APPEND,
		 Logical_list_MEM_VICE_VERCA_TheFunctional,NULL_EQ,list_nchotomy,MEM_MAP,MEM,list_nchotomy,
		 PileTally_to_PileTally_DEC2,bigger_than_cand_LogicallyOK,bigger_than_cand_LogicallyOK]

STRIP_TAC
    >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,MEM]
    >- STRIP_TAC
        >- 
 
 
 
               >-  (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                     >> `MEM y (MAP FST p)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. p = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d h ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                     >> `!d. MEM d h ==> MEM d (MAP FST p)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac [PileTally_to_PileTally_DEC2,bigger_than_cand_LogicallyOK])  
                    
                >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,MEM]  
                >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
                >-  metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
                >-  metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
                >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]   
                      >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM] 
                      >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy] 
                      >> `!d. MEM d p6 ==> MEM d l`
                           by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]  
                      >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally] 
                    >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota])    
                >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                     >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d p6 ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                     >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac [PileTally_to_PileTally_DEC2,bigger_than_cand_LogicallyOK])) 
                                   
             >- ((fs[Valid_Init_CandList_def,NULL,NULL_EQ,ALL_DISTINCT,
                 Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,
	         Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
		 EQE_REMOVE_ONE_CAND,ALL_DISTINCT_APPEND,
		 Logical_list_MEM_VICE_VERCA_TheFunctional] >> REPEAT STRIP_TAC)
               >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                     >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d p6 ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                     >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac [PileTally_to_PileTally_DEC2,bigger_than_cand_LogicallyOK])  
                  
                >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,MEM] 
                >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
                >-  metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
                >-  metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
                >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]   
                      >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM] 
                      >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy] 
                      >> `!d. MEM d p6 ==> MEM d l`
                           by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]  
                      >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally] 
                    >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota])    
                >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                     >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d p6 ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                     >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac [PileTally_to_PileTally_DEC2,bigger_than_cand_LogicallyOK]))) 
            >- rfs[ELIM_CAND_Auxiliary_dec_def])   
         >- rfs[ELIM_CAND_Auxiliary_dec_def]); 
 
(* --------------- transfer ----------------- *)

    (REPEAT STRIP_TAC     
      >> Cases_on `j1`)          
        >- (Cases_on `j2`                
          >- ((PairCases_on `p`       
              >> PairCases_on `p'`        
              >> rfs[TRANSFER_Auxiliary_dec_def,TRANSFER_Auxiliary_def] >>         
              fs[PileTally_to_PileTally_DEC1,Valid_PileTally_def,PileTally_to_PileTally_DEC2,NULL_EQ,NULL,
	      Valid_Init_CandList_def,LogicalLessThanQu_IMP_less_than_quota] >> REPEAT STRIP_TAC)  
               >- (`(!d. MEM d h \/ MEM d e ==> MEM d l) ==> (!d. MEM d (h++e) ==> MEM d l)`
               by  FULL_SIMP_TAC list_ss [MEM_APPEND] >>
               metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional])  
               >- metis_tac[LogicalLessThanQu_IMP_less_than_quota,Valid_PileTally_def])   
         >- fs[TRANSFER_Auxiliary_def]) 
       >- fs[TRANSFER_Auxiliary_def]); 







(REPEAT STRIP_TAC
  
    >> Cases_on `j1`)    
      >- (Cases_on `j2`  
             
          >-  ((PairCases_on`p` >> PairCases_on`p'`    
              >>  rfs [TRANSFER_Auxiliary_dec_def,TRANSFER_Auxiliary_def]
                 >> fs[NULL,NULL_EQ,Valid_Init_CandList_def,NULL_EQ,MEM_APPEND,
		       Logical_list_MEM_VICE_VERCA_TheFunctional,Valid_PileTally_def,
		       PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
		       less_than_qu_IMP_LogicalLessThanQuota]
                   >>  REPEAT STRIP_TAC)
		    >- metis_tac[MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
                    >- metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional] 
                    >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
		    >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]
		    >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
                    >- (`?L y. l = y::L` by metis_tac[NULL_EQ,list_nchotomy]
                     >> `MEM y (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally,MEM]
                     >> `?l1 q1. p'1 = q1::l1` by metis_tac [MEM_MAP,MEM,list_nchotomy]
                     >> `!d. MEM d p6 ==> MEM d l`
                         by metis_tac [MEM_APPEND,Logical_list_MEM_VICE_VERCA_TheFunctional]
		     >> `!d. MEM d p6 ==> MEM d (MAP FST p'1)` by metis_tac [PileTally_DEC2_IMP_PileTally]
                     >> metis_tac[PileTally_to_PileTally_DEC2,less_than_qu_IMP_LogicalLessThanQuota]))  
     >- rfs[TRANSFER_Auxiliary_dec_def])  
     >- rfs[TRANSFER_Auxiliary_dec_def]); 
 



 (* -----------------count ------------------------- *)


        

   (REPEAT STRIP_TAC
    >> Cases_on `j1`)
      >- (Cases_on `j2`
       >- (fs[COUNT_Auxiliary_def,COUNT_Auxiliary_dec_def] 
          >> metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,Valid_PileTally_def,
	    PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,Valid_Init_CandList_def,NULL_EQ,NULL])
       >- rfs[COUNT_Auxiliary_def])	    
      >- rfs[COUNT_Auxiliary_def]); 





 (REPEAT STRIP_TAC
    >> Cases_on `j1`)
        >- (Cases_on `j2` 
          >- (PairCases_on `p` >> PairCases_on`p'`
	        >> rfs[COUNT_Auxiliary_def,COUNT_Auxiliary_dec_def]
		 >> metis_tac[list_MEM_dec_def,Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,
		              Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
			      Valid_Init_CandList_def,NULL_EQ,NULL,Valid_PileTally_def,
			      PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] )
	  >- rfs[COUNT_Auxiliary_dec_def])
	>- rfs[COUNT_Auxiliary_dec_def]);  







(* --------------------------elect -----------------*)
(REPEAT STRIP_TAC 
   >> Cases_on`j1`)
     >- (Cases_on `j2`
       
      >- ((PairCases_on`p` >> PairCases_on`p'`
	   >> fs[ELECT_Auxiliary_def,ELECT_Auxiliary_dec_def] 
	   >> `take_append (p3 ++ l1) p3 = l1` by metis_tac [take_append_def,take_append_returns_appended] 
           >> `!d. MEM d p6 ==> MEM d (MAP FST p2) /\ MEM d (MAP FST p'2)` by metis_tac [MEM,Valid_PileTally_def]
           >> `(!c. MEM c l ==> MEM c (MAP FST p2))` by metis_tac [MEM,Valid_PileTally_def]
	   >> `(!c. MEM c p6 ==> MEM c (MAP FST p'2))` by metis_tac [MEM,Valid_PileTally_def] 
	   >> fs[logical_to_functional_BiggerThanQuota,bigger_than_quota_def,MEM,LENGTH_APPEND,
	               logical_to_functional_eqe_list_dec,eqe_list_dec2_verified,MEM,Valid_PileTally_def,
		        logical_to_functional_piles_eq,Valid_Init_CandList_def,list_nchotomy,NULL_EQ,
		       Valid_PileTally_def,PileTally_to_PileTally_DEC1,Valid_PileTally_def,
		       PileTally_to_PileTally_DEC2,Logical_list_MEM_VICE_VERCA_TheFunctional,MEM_APPEND,
		       logical_to_functional_update_pile] 
            >> REPEAT STRIP_TAC)     
	     >- (`!c. MEM c l1 ==> MEM c (MAP FST p'1)` by metis_tac [MEM, Valid_PileTally_def] 
	       >> metis_tac [logical_to_functional_BiggerThanQuota,bigger_than_quota_def,MEM]) 	       
             >- metis_tac [logical_to_functional_eqe_list_dec] 
	     >- metis_tac [eqe_list_dec2_verified]
             >- metis_tac [logical_to_functional_piles_eq,logical_to_functional_eqe_list_dec,
	                   eqe_list_dec2_verified]
             >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
             >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2] 
             >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
             >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
             >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2]
	     >- metis_tac [Valid_PileTally_def,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2])
	   >- rfs[ELECT_Auxiliary_def])   
         >- rfs[ELECT_Auxiliary_def]);


(REPEAT STRIP_TAC
    >> Cases_on `j1`)
      >- (Cases_on `j2` 
       >- ((PairCases_on`p` >> PairCases_on`p'`  
        >> rfs[ELECT_Auxiliary_dec_def,ELECT_Auxiliary_def]  
         >> MAP_EVERY qexists_tac [`take_append p'3 p3`]  
         >> REPEAT STRIP_TAC)   

>- metis_tac[NULL_EQ]  
          >- metis_tac [NULL_EQ]  
          >- RW_TAC bool_ss []  
          >- metis_tac [functional_to_logical_BiggerThanQuota]  
          >- rw []   
          >- metis_tac [list_eqe_dec_MEM1,MEM]   
          >- metis_tac [list_eqe_dec_MEM1,MEM]    
          >- metis_tac [eqe_list_dec2_verified,MEM] 
          >- metis_tac []   
          >- fs[]   
          >- metis_tac [list_eqe_dec_MEM1,MEM]  
          >- metis_tac [list_eqe_dec_MEM1]  
	  >-  metis_tac [eqe_list_dec2_verified]  
	  >- (`!c. MEM c h ==> MEM c l` by metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional]
            >> `!c. MEM c h ==> MEM c (MAP FST np)`
                by metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,MEM]
              >> `!c. MEM c h ==> MEM c (MAP FST p)`
                   by metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally,
                    MEM,Logical_list_MEM_VICE_VERCA_TheFunctional]
                >> metis_tac[Logical_list_MEM_VICE_VERCA_TheFunctional,functional_to_logical_piles_eq])
          >- rw[]      
          >- metis_tac [Valid_Init_CandList_def,NULL_EQ]  
          >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]  
          >-  metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally] 
          >- metis_tac [Valid_PileTally_def,PileTally_DEC1_to_PileTally,PileTally_DEC2_IMP_PileTally]  
          >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional]   
          >- metis_tac [Logical_list_MEM_VICE_VERCA_TheFunctional]  
          >- RW_TAC bool_ss [] 
	  >- fs[NULL_EQ])   
       >- fs[ELECT_Auxiliary_dec_def])
      >- fs[ELECT_Auxiliary_dec_def]); 
 

*)

val _ = export_theory ();
