open preamble
     AuxSpecTheory
     AuxIMPTheory
     AuxEquivProofsTheory
     AuxRulesSpecTheory
     AuxRulesIMPTheory
     AuxRulesEquivProofsTheory
     RulesSpecTheory
     RulesIMPTheory
     RulesProofTheory
     CheckerSpecTheory
     CheckerIMPTheory
 
val _ = new_theory "CheckerProofs";

val Initial_Judgement_IMP_TheLogical = Q.store_thm ("Initial_Judgement_IMP_TheLogical",
 `! l j. Initial_Judgement_dec l j ==> initial_judgement l j`,

  (REPEAT STRIP_TAC >> rw[initial_judgement_def]
    >> Cases_on `j`)

     >- (PairCases_on `p`
        >> MAP_EVERY qexists_tac [`p0`,`p1`,`p2`]
           >>  rfs[Initial_Judgement_dec_def,EVERY_MEM]
             >>  metis_tac[NULL_EQ])
     >- metis_tac[Initial_Judgement_dec_def]);
 

val Logical_to_Functional_Initial_Judgement = Q.store_thm ("Logical_to_Functional_Initial_Judgement",
 `! l j. initial_judgement l j ==> Initial_Judgement_dec l j`,

  (REPEAT STRIP_TAC
    >> rfs [initial_judgement_def]
      >> rw[Initial_Judgement_dec_def])
         >- FULL_SIMP_TAC list_ss [EVERY_MEM]
         >- FULL_SIMP_TAC list_ss [EVERY_MEM]);
 

val No_Valid_Step_After_Final = Q.store_thm("No_Valid_Step_After_Final",
 `! qu st h l w. ~ (Valid_Step (qu,st,l) (Final w) h)`,
 
 REPEAT STRIP_TAC
  >> rfs[Valid_Step_def]
        >- rfs[HWIN_dec_def] 
        >- rfs[EWIN_dec_def] 
        >- rfs[COUNT_dec_def] 
        >- rfs[TRANSFER_dec_def] 
        >- rfs[ELECT_dec_def] 
        >- rfs[ELIM_CAND_dec_def]
	>- rfs[TRANSFER_EXCLUDED_dec_def,TRANSFER_EXCLUDED_Auxiliary_dec_def]);  


val COUNT_thm = Q.store_thm("COUNT_thm",
  `COUNT_dec = COUNT`,
  simp[FUN_EQ_THM,Logical_Count_to_Functional,Functional_Count_to_Logical,FORALL_PROD,EQ_IMP_THM]);

val TRANSFER_thm = Q.store_thm("TRANSFER_thm",
  `TRANSFER_dec = TRANSFER`,
  simp[FUN_EQ_THM,Functional_Transfer_to_Logical_transfer,Logical_transfer_to_Functional_Transfer,FORALL_PROD,EQ_IMP_THM]);

val ELECT_thm = Q.store_thm("ELECT_thm",
  `ELECT_dec = ELECT`,
  simp[FUN_EQ_THM,Functional_to_Logical_elect,Logical_to_Functional_elect,FORALL_PROD,EQ_IMP_THM]);

val ELIM_CAND_thm = Q.store_thm("ELIM_CAND_thm",
  `ELIM_CAND_dec = ELIM_CAND`,
  simp[FUN_EQ_THM,Logical_elim_to_Functional_Elim,Functional_Elim_to_Logical_elim,FORALL_PROD,EQ_IMP_THM]);

val initial_judgement_thm = Q.store_thm("initial_judgement_thm",
  `Initial_Judgement_dec = initial_judgement`,
  rw[FUN_EQ_THM,Initial_Judgement_IMP_TheLogical,Logical_to_Functional_Initial_Judgement,EQ_IMP_THM]);
   
val valid_judgements_thm = Q.store_thm("valid_judgements_thm",
  `valid_judgements_dec = valid_judgements`,
  rw[FUN_EQ_THM,valid_judgements_dec_LRC,valid_judgements_def,EQ_IMP_THM] \\ rw[]
  >- (
   fs[APPEND_EQ_APPEND] \\ rw[] \\ fs[LRC_APPEND,LRC_def]
   \\ TRY(last_x_assum(assume_tac o Q.AP_TERM`LENGTH`) \\ fs[] \\ NO_TAC)
   \\ TRY (
     qpat_x_assum`Valid_Step _ j0 j1`mp_tac
     \\ simp[Valid_Step_def,HWIN_thm,EWIN_thm,COUNT_thm,TRANSFER_thm,ELECT_thm,ELIM_CAND_thm,EXISTS_MEM,TRANSFER_EXCLUDED_thm]
     \\ NO_TAC)
   \\ first_assum(mp_tac o SYM o Q.AP_TERM`LENGTH`)
   \\ simp_tac std_ss [LENGTH,LENGTH_EQ_NUM_compute]
   \\ rw[APPEND_EQ_SING] \\ fs[] \\ rw[] \\ fs[LRC_def] \\ rw[]
   \\ qpat_x_assum`Valid_Step _ j0 _` mp_tac
   \\ simp[Valid_Step_def,HWIN_thm,EWIN_thm,COUNT_thm,TRANSFER_thm,ELECT_thm,ELIM_CAND_thm,EXISTS_MEM,TRANSFER_EXCLUDED_thm])
  >- (
    qmatch_assum_rename_tac`ls ≠ []`
    \\ Q.ISPEC_THEN`ls`FULL_STRUCT_CASES_TAC SNOC_CASES \\ fs[] \\ rw[]
    \\ qexists_tac`HD(l++[Final w])`
    \\ Induct_on`l` \\ rw[LRC_def]
    \\ last_x_assum mp_tac
    \\ impl_tac
    >- (
      rw[] \\ fs[]
      \\ first_x_assum(qspec_then`h::J0`mp_tac)
      \\ rw[] )
    \\ rw[]
    \\ qexists_tac`HD(l++[Final w])`
    \\ rw[]
    \\ first_x_assum(qspec_then`[]`mp_tac)
    \\ rw[]
    \\ Cases_on`l ++ [Final w]` \\ fs[]
    \\ rw[Valid_Step_def,HWIN_thm,EWIN_thm,COUNT_thm,TRANSFER_thm,ELECT_thm,ELIM_CAND_thm,EXISTS_MEM,TRANSFER_EXCLUDED_thm]
    \\ metis_tac[] )
);

val Valid_intermediate_judgements_thm = Q.store_thm ("Valid_intermediate_judegments_thm",
 `Valid_intermediate_judgements = valid_judgements`,
   rw[FUN_EQ_THM,valid_judgements_def,Valid_intermediate_judgements_def,Valid_Step_Spec_def]);
 
val Check_Parsed_Certificate_iff_Valid_Certificate = Q.store_thm ("Check_Parsed_Certificate_iff_Valid_Certificate",
 `! params J. Check_Parsed_Certificate params J = Valid_Certificate params J`,

  Cases_on `J`
    >- rw[Check_Parsed_Certificate_def,Valid_Certificate_def]
    >- metis_tac [Check_Parsed_Certificate_def,Valid_Certificate_def,Valid_intermediate_judgements_thm,valid_judgements_thm,initial_judgement_thm]);
 


val _ = export_theory ();
