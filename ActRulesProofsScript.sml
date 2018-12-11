open preamble
     AuxSpecTheory
     AuxBoolTheory
     AuxEquivProofsTheory
     AuxRulesSpecTheory
     AuxRulesBoolTheory
     AuxRulesEquivProofsTheory
     ActRulesSpecTheory
     ActRulesBoolTheory
                          

val _ = new_theory "ActRulesProofs";
     

val EWIN_thm = Q.store_thm("EWIN_thm",
  `EWIN_dec = EWIN`,
  simp[FUN_EQ_THM]
  \\ qx_gen_tac`params`
  \\ PairCases_on`params`
  \\ Cases \\ Cases
  \\ rw[EWIN_def,EWIN_dec_def]
  \\ PairCases_on`p`
  \\ rw[EWIN_def,EWIN_dec_def] 
  \\ metis_tac[]);
  
val HWIN_thm = Q.store_thm("HWIN_thm",
  `HWIN_dec = HWIN`, 
  simp[FUN_EQ_THM]
  \\ qx_gen_tac`params`
  \\ PairCases_on`params`
  \\ Cases \\ Cases \\ rw[HWIN_def,HWIN_dec_def]
  \\ PairCases_on`p`
  \\ rw[HWIN_def,HWIN_dec_def]
  \\ metis_tac[HWIN_def,HWIN_dec_def])
 
val Logical_elim_to_Functional_ELIM = Q.store_thm("Logical_elim_to_Functional_Elim",
 `!c qu st l j1 j2. ELIM_CAND c (qu,st,l) j1 j2 ==> ELIM_CAND_dec c (qu,st,l) j1 j2`,
  
 REPEAT STRIP_TAC  
   >> fs[ELIM_CAND_def,ELIM_CAND_dec_def] 
    >> fs[Logical_ElimAux_to_Functional]   
     >> fs[ELIM_CAND_Auxiliary_def,EQE_IMP_REMOVE_ONE_CAND]   
     >> `MEM c (MAP FST t)` by metis_tac [Valid_PileTally_def,FST,MAP]
     >> `!d. MEM d h ==> MEM d (MAP FST t)` by metis_tac [Valid_PileTally_def]
     >> `!d. (d = c) ==> ?l. MEM (c,l) p`
              by metis_tac[GET_CAND_PILE_MEM,Valid_PileTally_def]
     >> metis_tac [Logical_subpile1_IMP_TheFunctional,Logical_subpile2_IMP_TheFunctional]);
      
       
val Functional_Elim_to_Logical_elim = Q.store_thm("Functional_Elim_to_Logical_elim",
 `!c qu st l j1 j2. ELIM_CAND_dec c (qu,st,l) j1 j2 ==> ELIM_CAND c (qu,st,l) j1 j2`,
 
 Cases_on `j1`
   >- (Cases_on `j2` 
      >- (REPEAT STRIP_TAC >> PairCases_on `p` >> PairCases_on `p'` 
         \\ fs[ELIM_CAND_dec_def,ELIM_CAND_def]
	 \\ metis_tac[NULL,NULL_EQ,Functional_ElimAux_to_Logical,Functional_subpile1_IMP_TheLogical,
	              Functional_subpile2_IMP_TheLogical,EQE_REMOVE_ONE_CAND,ALL_DISTINCT_APPEND])
      >- rfs[ELIM_CAND_dec_def])	    
  >- rfs[ELIM_CAND_dec_def]);

  
val Functional_Transfer_to_Logical_transfer = Q.store_thm("Functional_Transfer_to_Logical_transfer",
 `! st qu l j1 j2. TRANSFER_dec (qu,st,l) j1 j2 ==> TRANSFER (qu,st,l) j1 j2`,

 Cases_on `j1`  
   >- (Cases_on `j2`    
    >- ((REPEAT STRIP_TAC >> PairCases_on `p` >> PairCases_on `p'` 
      >> fs[TRANSFER_dec_def,TRANSFER_def]  
      >> Cases_on `p3`)  
        >- fs[]      
        >- (rfs[NULL,NULL_EQ]
	  >> metis_tac[NULL,NULL_EQ,Logical_TransferAux_to_Functional,Functional_subpile1_IMP_TheLogical,
	              Functional_subpile2_IMP_TheLogical,NULL_EQ,NULL,Functional_TransferAux_to_Logical,
		      TRANSFER_Auxiliary_dec_def]))
    >- rfs[TRANSFER_dec_def])
    >- rfs[TRANSFER_dec_def]);
 
   
val Logical_transfer_to_Functional_Transfer = Q.store_thm("Logical_transfer_to_Functional_Transfer",
 `! st qu l j1 j2. TRANSFER (qu,st,l) j1 j2 ==> TRANSFER_dec (qu,st,l) j1 j2`,
 
  REPEAT STRIP_TAC
   >> fs[TRANSFER_def,TRANSFER_dec_def]   
    >> `MEM c (MAP FST np)` by metis_tac[MEM_MAP,FST,TRANSFER_Auxiliary_def]
      >> `!d. (d = c) ==> ?l. MEM (c,l) np` by metis_tac[GET_CAND_PILE_MEM,Valid_PileTally_def]
       >> metis_tac[Logical_TransferAux_to_Functional,    
             Logical_subpile1_IMP_TheFunctional,Logical_subpile2_IMP_TheFunctional,TRANSFER_Auxiliary_def,
	     GET_CAND_PILE_MEM,Valid_PileTally_def,MEM_MAP]);   
        
       
val Functional_to_Logical_elect = Q.store_thm("Functional_to_Logical_elect",
 `! st qu l j1 j2. ELECT_dec (qu,st,l) j1 j2 ==> ELECT (qu,st,l) j1 j2`,
  
 Cases_on `j1`  
  >- (Cases_on `j2`     
     >- (REPEAT STRIP_TAC >> PairCases_on`p` >> PairCases_on`p'`  
      >> fs[ELECT_dec_def,ELECT_def]   
       >> MAP_EVERY qexists_tac [`DROP (LENGTH p3) p'3`] 
        >> `p'3 = p3 ++ (DROP (LENGTH p3) p'3)` by
          metis_tac[ELECT_Auxiliary_dec_def,TAKE_DROP,DROP_LENGTH,TAKE_DROP_LENGTH_BACKLOG,APPEND_11] 
        >> `!c. MEM c (DROP (LENGTH p3) p'3) ==> MEM c (MAP FST p2)`
           by metis_tac[ELECT_Auxiliary_dec_def,MEM,MEM_APPEND,Valid_PileTally_def,PileTally_DEC1_to_PileTally,
              PileTally_DEC2_IMP_PileTally,Valid_Init_CandList_def,eqe_list_dec2_verified,
             list_eqe_dec_MEM1,Valid_PileTally_def,Valid_PileTally_def,
             Logical_list_MEM_VICE_VERCA_TheFunctional,eqe_list_dec2_verified]
        >> `!c. MEM c (DROP (LENGTH p3) p'3) ==> MEM c (MAP FST p'2)`
           by metis_tac[ELECT_Auxiliary_dec_def,MEM,MEM_APPEND,Valid_PileTally_def,PileTally_DEC1_to_PileTally,
              PileTally_DEC2_IMP_PileTally,Valid_Init_CandList_def,eqe_list_dec2_verified,
             list_eqe_dec_MEM1,Valid_PileTally_def,Valid_PileTally_def,
             Logical_list_MEM_VICE_VERCA_TheFunctional,eqe_list_dec2_verified]
        >> metis_tac[Functional_ElectAux_to_Logical,ELECT_Auxiliary_dec_def,ALL_NON_EMPTY_def,ALL_NON_ZERO_def,
         Functional_AllNonEmpty_to_Logical,Functional_AllNonZero_to_Logical,
         GET_CAND_PILE_MEM,Functional_AllNonEmpty_to_Logical,GET_CAND_PILE_MEM,
         EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
         Valid_PileTally_def,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional,
         eqe_list_dec2_verified,EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,
         PileTally_to_PileTally_DEC2,Valid_PileTally_def,Valid_PileTally_def,
         Logical_list_MEM_VICE_VERCA_TheFunctional,eqe_list_dec2_verified,functional_to_logical_update_pile_ACT])
     >- rfs[ELECT_dec_def]) 
  >- rfs[ELECT_dec_def]);     
    
      
val Logical_to_Functional_elect = Q.store_thm ("Logical_to_Functional_elect",
 `! st qu l j1 j2. ELECT (qu,st,l) j1 j2 ==> ELECT_dec (qu,st,l) j1 j2`,

 REPEAT STRIP_TAC  
  >> fs[ELECT_def,ELECT_dec_def] 
  >> `DROP (LENGTH bl) (bl ++ l1) = l1` by metis_tac[DROP_LENGTH]
  >> fs[Logical_ElectAux_to_Functional] 
  >> rfs[ELECT_Auxiliary_def]  
  >> `!c. MEM c l1 ==> MEM c (MAP FST p)`
       by metis_tac [ELECT_Auxiliary_def,MEM,Valid_PileTally_def]
  >> `!c. MEM c l1 ==> MEM c (MAP FST np)`
       by metis_tac [ELECT_Auxiliary_def,MEM,Valid_PileTally_def]
  >> fs[logical_to_functional_update_pile_ACT]
  >> metis_tac[Logical_AllNonZero_to_Functional,
                MEM,ELECT_Auxiliary_def,Logical_AllNonEpty_to_Functional])   
             
  
val Functional_Count_to_Logical = Q.store_thm("Functional_Count_to_Logical",
 `! st qu l j1 j2. COUNT_dec (qu,st,l) j1 j2 ==> COUNT (qu,st,l) j1 j2`,
 
 Cases_on `j1` 
  >- (Cases_on `j2`   
     >- (REPEAT STRIP_TAC >> PairCases_on`p` >> PairCases_on`p'`   
      >> fs[COUNT_dec_def,COUNT_def]   
       >> metis_tac[Functional_COUNTAux_to_Logical,NULL,NULL_EQ,
                    Functional_to_Logical_Count_Dec_Aux,COUNT_Auxiliary_dec_def,COUNTAux_dec_def])
     >- rfs[COUNT_dec_def]) 
   >- rfs[COUNT_dec_def]);  
       

val Logical_Count_to_Functional = Q.store_thm("Logical_Count_to_Functional",
 `! st qu l j1 j2. COUNT (qu,st,l) j1 j2 ==> COUNT_dec (qu,st,l) j1 j2`,

 REPEAT STRIP_TAC
  >> fs[COUNT_def,COUNT_dec_def]   
   >> metis_tac[Logical_CountAux_to_Functional,Logical_to_Functional_Count_Dec_Aux,
                Logical_CountAux_to_Functional,COUNT_Auxiliary_def]);

 
val TRANSFER_EXCLUDED_Auxiliary_thm = Q.store_thm("TRANSFER_EXCLUDED_Auxiliary_thm",
 `TRANSFER_EXCLUDED_Auxiliary_dec = TRANSFER_EXCLUDED_Auxiliary`,
   simp[FUN_EQ_THM,Logical_TransferExcludedAux_to_Functional,Functional_TransferExcluded_Aux_to_Logical,
        FORALL_PROD,EQ_IMP_THM]);


val TRANSFER_EXCLUDED_thm = Q.store_thm("TRANSFER_EXCLUDED_thm",
   `TRANSFER_EXCLUDED_dec = TRANSFER_EXCLUDED`,

        (simp[FUN_EQ_THM]
          >> qx_gen_tac`params`
          >> PairCases_on`params`
           >>  Cases)
             >-(Cases
               >- (PairCases_on`p`
                   >> PairCases_on `p'`
                    >> simp[TRANSFER_EXCLUDED_dec_def,TRANSFER_EXCLUDED_def,TRANSFER_EXCLUDED_Auxiliary_thm])
                     >- simp[TRANSFER_EXCLUDED_dec_def,TRANSFER_EXCLUDED_def,TRANSFER_EXCLUDED_Auxiliary_thm])
                     >- simp[TRANSFER_EXCLUDED_dec_def,TRANSFER_EXCLUDED_def,TRANSFER_EXCLUDED_Auxiliary_thm]);


 (*
val TRANSFER_EXCLUDED_thm = Q.store_thm("TRANSFER_EXCLUDED_thm",
   `TRANSFER_EXCLUDED_dec = TRANSFER_EXCLUDED`,

        (simp[FUN_EQ_THM]
          >> qx_gen_tac`params`
          >> PairCases_on`params`
           >>  Cases)
             >-(Cases
               >- (PairCases_on`p`
                   >> PairCases_on `p'`
                    >> simp[TRANSFER_EXCLUDED_dec_def,TRANSFER_EXCLUDED_def,TRANSFER_EXCLUDED_Auxiliary_thm])
                     >- simp[TRANSFER_EXCLUDED_dec_def,TRANSFER_EXCLUDED_def,TRANSFER_EXCLUDED_Auxiliary_thm])
                     >- simp[TRANSFER_EXCLUDED_dec_def,TRANSFER_EXCLUDED_def,TRANSFER_EXCLUDED_Auxiliary_thm]);

*)


val _ = export_theory ();
