open preamble
     AuxSpecTheory
     AuxIMPTheory
     AuxEquivProofsTheory
     AuxRulesSpecTheory
     AuxRulesIMPTheory
     AuxRulesEquivProofsTheory
     RulesSpecTheory
     RulesIMPTheory 
                    
                                    
(* the proofs in this file work for any of the formalised rules of particular STV algorithms. One only needs to call the right dependencies in. For example, here we have called UnionRules *)

 
val _ = new_theory "RulesProofs";
        
val EWIN_thm = Q.store_thm("EWIN_thm",
  `EWIN_dec = EWIN`,
  simp[FUN_EQ_THM] 
  \\ qx_gen_tac`params`  
  \\ PairCases_on`params`  
  \\ Cases
    >- (Cases   
      >- (rw[EWIN_def,EWIN_dec_def] \\ rw[EWIN_Auxiliary_dec_def,EWIN_Auxiliary_def])   
      >- (PairCases_on`p` \\ rw[EWIN_def,EWIN_dec_def] \\ rw[EWIN_Auxiliary_thm]))   
    >- (rw[EWIN_dec_def,EWIN_def] \\ rw[EWIN_Auxiliary_dec_def,EWIN_Auxiliary_def]));
 
val HWIN_thm = Q.store_thm("HWIN_thm",
  `HWIN_dec = HWIN`,

  simp[FUN_EQ_THM]
  \\ qx_gen_tac`params`
  \\ PairCases_on`params`
  \\ Cases
    >- (Cases
      >- (rw[HWIN_def,HWIN_dec_def] \\ rw[HWIN_Auxiliary_thm]
       \\ (try rw[EWIN_Auxiliary_thm]))
      >- (PairCases_on`p` \\ rw[HWIN_dec_def,HWIN_def] \\ rw[HWIN_Auxiliary_thm]
       \\ try (rw[EWIN_Auxiliary_thm])))
    >- (rw[HWIN_dec_def,HWIN_def] \\ rw[HWIN_Auxiliary_dec_def,HWIN_Auxiliary_def]
        \\ try (rw[EWIN_Auxiliary_dec_def,EWIN_Auxiliary_def])));
 
val _ = mesonLib.max_depth := 15; 
    
val Logical_elim_to_Functional_ELIM = Q.store_thm("Logical_elim_to_Functional_Elim",
 `!c qu st l j1 j2. ELIM_CAND c (qu,st,l) j1 j2 ==> ELIM_CAND_dec c (qu,st,l) j1 j2`,
  
 REPEAT STRIP_TAC
   >> fs[ELIM_CAND_def, ELIM_CAND_dec_def]
    >> fs[Logical_ElimAux_to_Functional]
     >> fs[ELIM_CAND_Auxiliary_def] 
      >> ((mesonLib.ASM_MESON_TAC [NULL,NULL_EQ,ELIM_CAND_Auxiliary_def,PILES_EQ_to_Spec,Spec_to_PILES_EQ])
         ORELSE
          ((Cases_on`FLAT (get_cand_pile c p)`
           >- (simp[] >> mesonLib.ASM_MESON_TAC [Logical_to_Functional_subpile2Backlog_trans,MEM])
           >- (simp[] >> mesonLib.ASM_MESON_TAC [Logical_to_Functional_subpile2Backlog_trans,MEM]))
            ORELSE
             metis_tac [Logical_subpile1_IMP_TheFunctional,Logical_subpile2_IMP_TheFunctional,
                        MEM,GET_CAND_PILE_MEM,Valid_PileTally_def])));
    
     
val Logical_elim_to_Functional_ELIM = Q.store_thm("Logical_elim_to_Functional_Elim",
 `!c qu st l j1 j2. ELIM_CAND c (qu,st,l) j1 j2 ==> ELIM_CAND_dec c (qu,st,l) j1 j2`,
  
 REPEAT STRIP_TAC    
   >> fs[ELIM_CAND_def, ELIM_CAND_dec_def]  
    >> fs[Logical_ElimAux_to_Functional]
     >> fs[ELIM_CAND_Auxiliary_def] 
      >> ((mesonLib.ASM_MESON_TAC [PILES_EQ_to_Spec,Spec_to_PILES_EQ])   
         ORELSE
	 ((Cases_on`FLAT (get_cand_pile c p)`
          >- (simp[] >> mesonLib.ASM_MESON_TAC [Logical_to_Functional_subpile2Backlog_trans,MEM])
          >- (simp[] >> mesonLib.ASM_MESON_TAC [Logical_to_Functional_subpile2Backlog_trans,MEM]))
           ORELSE
 	     metis_tac [Logical_subpile1_IMP_TheFunctional,Logical_subpile2_IMP_TheFunctional,
                        MEM,GET_CAND_PILE_MEM,Valid_PileTally_def])));            
   
 
val NON_Empty_list = Q.store_thm("NON_Empty_list",
 `!l. l <> [] ==> ?l0 ls. l = l0 :: ls`,
Induct_on `l`
     >- rw[]
     >- metis_tac[]);
    
val _ = mesonLib.max_depth := 15;
                
val Functional_Elim_to_Logical_elim = Q.store_thm("Functional_Elim_to_Logical_elim",
 `!c qu st l j1 j2. ELIM_CAND_dec c (qu,st,l) j1 j2 ==> ELIM_CAND c (qu,st,l) j1 j2`,
    
Cases_on `j1`       
   >- (Cases_on `j2`        
      >- (REPEAT STRIP_TAC >> PairCases_on `p` >> PairCases_on `p'` 
         \\ fs[ELIM_CAND_dec_def,ELIM_CAND_def]
	 \\ fs[NULL,NULL_EQ,Functional_ElimAux_to_Logical,MEM,EQE_REMOVE_ONE_CAND,
	       ALL_DISTINCT_APPEND] 
	 \\ ((mesonLib.ASM_MESON_TAC [PILES_EQ_to_Spec,Spec_to_PILES_EQ])               
            ORELSE
	    ((mesonLib.ASM_MESON_TAC [Functional_subpile1_IMP_TheLogical,
	     Functional_subpile2_IMP_TheLogical])  
	    ORELSE 
	     (Cases_on`FLAT (get_cand_pile c p2)`
              >- (fs[NULL,NULL_EQ]
	       >> mesonLib.ASM_MESON_TAC [ELIM_CAND_Auxiliary_dec_def,Functional_to_Logical_subpile2_backlog_trans2,MEM])  
              >- (fs[NULL,NULL_EQ,NON_Empty_list]
	       >> mesonLib.ASM_MESON_TAC [ELIM_CAND_Auxiliary_dec_def,Functional_to_Logical_subpile2_backlog_trans2,MEM]))))) 
     >- rfs[ELIM_CAND_dec_def])
  >- rfs[ELIM_CAND_dec_def]);
      
  
val _ = mesonLib.max_depth := 10;
       
     
val Functional_Transfer_to_Logical_transfer = Q.store_thm("Functional_Transfer_to_Logical_transfer",
 `! st qu l j1 j2. TRANSFER_dec (qu,st,l) j1 j2 ==> TRANSFER (qu,st,l) j1 j2`,
   
 Cases_on `j1`         
   >- (Cases_on `j2`               
    >- ((REPEAT STRIP_TAC >> PairCases_on `p` >> PairCases_on `p'`  
      >> fs[TRANSFER_dec_def,TRANSFER_def]        
      >> Cases_on `p3`)             
        >- fs[]                 
        >- (rfs[NULL,NULL_EQ,Logical_TransferAux_to_Functional,Logical_list_MEM_VICE_VERCA_TheFunctional]  
         >> fs[Functional_TransferAux_to_Logical] 
	 >> ((mesonLib.ASM_MESON_TAC [ALL_EMPTY_Gives_Spec,List_Diff_to_Spec])       
          ORELSE
	  (mesonLib.ASM_MESON_TAC[Functional_TransferAux_to_Logical,TRANSFER_Auxiliary_dec_def,
	     MEM_MAP,GET_CAND_PILE_MEM,EVERY_CAND_HAS_ONE_PILE,MEM,Logical_list_MEM_VICE_VERCA_TheFunctional,
	     Functional_subpile1_IMP_TheLogical,MEM,Functional_subpile2_IMP_TheLogical,
             TRANSFER_Auxiliary_dec_def]
         ORELSE   
	  metis_tac[NULL,NULL_EQ,Logical_TransferAux_to_Functional,
	       Functional_subpile1_IMP_TheLogical,TRANSFER_Auxiliary_dec_def,
               Functional_subpile2_IMP_TheLogical,Functional_TransferAux_to_Logical,
	       TRANSFER_Auxiliary_dec_def,MEM,subpile1_BlMem_trans2_IsCorrect, 
	       Functional_to_Logical_subpile1BacklogTrans2,
	       Functional_to_Logical_subpile2_backlog_trans2]))))     
    >- rfs[TRANSFER_dec_def])
    >- rfs[TRANSFER_dec_def]); 
      
 
val _ = mesonLib.max_depth := 22; 
        
                    
val Logical_transfer_to_Functional_Transfer = Q.store_thm("Logical_transfer_to_Functional_Transfer",
 `! st qu l j1 j2. TRANSFER (qu,st,l) j1 j2 ==> TRANSFER_dec (qu,st,l) j1 j2`,
    
  REPEAT STRIP_TAC
   >> fs[TRANSFER_def,TRANSFER_dec_def]    
   >> fs[Logical_TransferAux_to_Functional,NULL,NULL_EQ]
    >> ((mesonLib.ASM_MESON_TAC [Spec_Gives_ALL_EMPTY,Spec_to_List_Diff])  
     ORELSE
     ((`MEM c (MAP FST np)` by metis_tac[MEM_MAP,FST,MEM,TRANSFER_Auxiliary_def]     
      >> `!d. (d = c) ==> ?l. MEM (c,l) np` by metis_tac[GET_CAND_PILE_MEM,Valid_PileTally_def]
       >> mesonLib.ASM_MESON_TAC[Logical_TransferAux_to_Functional,    
             Logical_subpile1_IMP_TheFunctional,Logical_subpile2_IMP_TheFunctional,TRANSFER_Auxiliary_def,
	     GET_CAND_PILE_MEM,Valid_PileTally_def,MEM_MAP])
        ORELSE   
	 (metis_tac[TRANSFER_Auxiliary_def,subpile1_BlMem_trans2_IsCorrect,MEM,
              Logical_to_Functional_subpileBacklogTrans2,Logical_to_Functional_subpile2Backlog_trans]))));
                         
            
val Functional_to_Logical_elect = Q.store_thm("Functional_to_Logical_elect",
 `! st qu l j1 j2. ELECT_dec (qu,st,l) j1 j2 ==> ELECT (qu,st,l) j1 j2`,
  
 Cases_on `j1`  
  >- (Cases_on `j2`       
     >- (REPEAT STRIP_TAC >> PairCases_on`p` >> PairCases_on`p'` 
      >> fs[ELECT_dec_def,ELECT_def]
       >> ((mesonLib.ASM_MESON_TAC [NULL_EQ,NULL,Functional_ElectAux_to_Logical])  
        ORELSE
	(MAP_EVERY qexists_tac [`DROP (LENGTH p3) p'3`] 
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
        >> metis_tac[Functional_ElectAux_to_Logical,ELECT_Auxiliary_dec_def,NULL,NULL_EQ,ALL_NON_EMPTY_def,
	 ALL_NON_ZERO_def,
         Functional_AllNonEmpty_to_Logical,Functional_AllNonZero_to_Logical,
         GET_CAND_PILE_MEM,Functional_AllNonEmpty_to_Logical,GET_CAND_PILE_MEM,
         EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
         Valid_PileTally_def,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional,
         eqe_list_dec2_verified,EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,
         PileTally_to_PileTally_DEC2,Valid_PileTally_def,Valid_PileTally_def,
         Logical_list_MEM_VICE_VERCA_TheFunctional,eqe_list_dec2_verified,functional_to_logical_update_pile_ACT,
	 functional_to_logical_update_pile]))) 
   >- rfs[ELECT_dec_def]) 
  >- rfs[ELECT_dec_def]);	 
   	  
       
val Logical_to_Functional_elect = Q.store_thm ("Logical_to_Functional_elect",
 `! st qu l j1 j2. ELECT (qu,st,l) j1 j2 ==> ELECT_dec (qu,st,l) j1 j2`,
 
REPEAT STRIP_TAC
  >> fs[ELECT_def,ELECT_dec_def] 
  >> `DROP (LENGTH bl) (bl ++ l1) = l1` by metis_tac[DROP_LENGTH]  
  >> fs[Logical_ElectAux_to_Functional]  
  >> try (rfs[ELECT_Auxiliary_def]  
   >> `!c. MEM c l1 ==> MEM c (MAP FST p)`
       by metis_tac [ELECT_Auxiliary_def,MEM,Valid_PileTally_def]  
   >> `!c. MEM c l1 ==> MEM c (MAP FST np)`
       by metis_tac [ELECT_Auxiliary_def,MEM,Valid_PileTally_def]   
   >> fs[Logical_AllNonEpty_to_Functional,logical_to_functional_update_pile_ACT,logical_to_functional_update_pile]))
     
   
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
    
 
 

(*
val TRANSFER_EXCLUDED_Auxiliary_thm = Q.store_thm("TRANSFER_EXCLUDED_Auxiliary_thm",
 `TRANSFER_EXCLUDED_Auxiliary_dec = TRANSFER_EXCLUDED_Auxiliary`,
   simp[FUN_EQ_THM,Logical_TransferExcludedAux_to_Functional,Functional_TransferExcluded_Aux_to_Logical,
        FORALL_PROD,EQ_IMP_THM]);
*)

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





val _ = export_theory ();
