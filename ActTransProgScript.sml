open preamble  basis AuxSpecTheory  AuxBoolTheory AuxEquivProofsTheory
     AuxRulesBoolTheory  ActRulesBoolTheory ActCheckerBoolTheory 
  
  
val _ = new_theory "ActTransProg";

val _ = translation_extends"basisProg";
  
 
val r = translate SUM_RAT_def;

val r = translate get_cand_tally_def;
 
val r = translate less_than_quota_def;
val r = translate equal_except_dec_def;
val r = translate bigger_than_cand_def; 
val r = translate get_cand_pile_def;

val () = use_mem_intro := true;
 
val r = translate list_MEM_dec_def;
 
val r = translate Valid_PileTally_dec1_def;
val r = translate Valid_PileTally_dec2_def;
val r = translate subpile1_def;
val r = translate subpile2_def;
val r = translate ELIM_CAND_Auxiliary_dec_def;
(* val r = translate ELIM_CAND_dec_def; *)   

val r = translate subpile1_BlMem_trans2_def;
val r = translate subpile1_backlog_trans2_def;
val r = translate subpile2_backlog_trans2_def;

val r = translate ELIM_CAND_dec_def;

val r = translate first_continuing_cand_dec_def;  
val r = translate COUNTAux_dec_def; 
val r = translate COUNT_Auxiliary_dec_def;
val r = translate COUNT_dec_def;  

val r = translate get_cand_pile_list_def;

val r = translate TRANSFER_Auxiliary_dec_def;
val r = translate TRANSFER_dec_def;
  
val r = translate eqe_list_dec_def;
val r = translate eqe_list_dec2_def;
val r = translate piles_eq_list_def;
  
val r = translate DROP_def;
val r = translate TAKE_def;

val r = translate Count_Occurrences_def;
val r = translate ReGroup_Piles_def;
  
val r = translate pairTheory.PAIR_MAP;
val r = translate PART3_DEF;
val r = translate QSORT3_DEF;
val r = translate TRANSFER_EXCLUDED_Auxiliary_dec_def;
val r = translate TRANSFER_EXCLUDED_dec_def;
 
val () = use_mem_intro := false;

val r = translate HWIN_dec_def;
val r = translate EWIN_dec_def;

val r = translate SORTED_DEF;
val r = translate tally_comparison_def;
val r = translate bigger_than_quota_def;
  
val r =translate ELECT_Auxiliary_dec_def;
 
val r = translate ALL_NON_EMPTY_def;
val r = translate ALL_NON_ZERO_def;

val all_non_zero_side_def = fetch"-""all_non_zero_side_def";

val r = translate ACT_TransValue_def;
val r = translate update_cand_transVal_ACT_def;
val r = translate update_cand_pile_ACT_def;


val r = translate ELECT_dec_def;
 
 
val act_transvalue_side_def = fetch"-""act_transvalue_side_def";
val update_cand_transval_act_side_def = fetch"-""update_cand_transval_act_side_def";
val update_cand_pile_act_side_def = fetch"-""update_cand_pile_act_side_def";
val elect_dec_side_def = fetch"-""elect_dec_side_def";  

val all_non_zero_side = Q.prove(
 `! v3 v2. EVERY(\x. (get_cand_pile x v3) <> []) v2 ==> all_non_zero_side v3 v2`,
  Induct_on `v2`
    >- rw[all_non_zero_side_def]
    >- (rw[MEM] >> fs[all_non_zero_side_def] >> metis_tac[MEM])) |> update_precondition;
  

val act_transvalue_side = Q.prove(
 `! v4 v6 v5 v3. SUM_RAT (LAST (get_cand_pile v3 v4)) <> 0 /\ (get_cand_pile v3 v4 <> [])
          ==> act_transvalue_side v4 v6 v5 v3`,
   rw[act_transvalue_side_def]) |> update_precondition;


val update_cand_transval_act_side = Q.prove(
 `! v4 v2 v5 v3. (get_cand_pile v2 v3 <> []) /\ (SUM_RAT (LAST (get_cand_pile v2 v3)) <> 0)
                  ==> update_cand_transval_act_side v4 v2 v5 v3`,
   rw[update_cand_transval_act_side_def]
    >> rw[act_transvalue_side]) |> update_precondition;

val update_cand_pile_act_side = Q.prove(
 `! a0 a1 a2 a3 a4.
  EVERY(\x. (get_cand_pile x a3 <> [])) a2 /\ EVERY(\x. (get_cand_pile x a4 <> [])) a2 /\
  EVERY(\y. (SUM_RAT (LAST (get_cand_pile y a3)) <> 0)) a2 /\
  EVERY(\y. (SUM_RAT (LAST (get_cand_pile y a4)) <> 0)) a2
       ==> update_cand_pile_act_side a0 a1 a2 a3 a4`,

         Induct_on `a2`
  \\ rw[Once update_cand_pile_act_side_def,update_cand_transval_act_side_def]
    \\ rw[act_transvalue_side_def]) |> update_precondition;


val elect_dec_side = Q.prove(
  `elect_dec_side a b c = T`,
  rw[definition"elect_dec_side_def"] 
    >- (rw[all_non_zero_side_def] >> fs[ELECT_Auxiliary_dec_def]  
      >>`!c. MEM c (DROP (LENGTH v11) v23) ==> MEM c (MAP FST v13)`
        by metis_tac[MEM,MEM_APPEND,Valid_PileTally_def,PileTally_DEC1_to_PileTally,
        PileTally_DEC2_IMP_PileTally,Valid_Init_CandList_def,eqe_list_dec2_verified,
        list_eqe_dec_MEM1,Valid_PileTally_def,Valid_PileTally_def,
        Logical_list_MEM_VICE_VERCA_TheFunctional,eqe_list_dec2_verified]
      >> metis_tac[ALL_NON_EMPTY_def,Functional_AllNonEmpty_to_Logical,GET_CAND_PILE_MEM,
         EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
         Valid_PileTally_def,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional,
         eqe_list_dec2_verified])

     >- (rw[all_non_zero_side_def] >> fs[ELECT_Auxiliary_dec_def] 
      >>`!c. MEM c (DROP (LENGTH v11) v23) ==> MEM c (MAP FST v25)`
        by metis_tac[MEM,MEM_APPEND,Valid_PileTally_def,PileTally_DEC1_to_PileTally,
        PileTally_DEC2_IMP_PileTally,Valid_Init_CandList_def,eqe_list_dec2_verified,
        list_eqe_dec_MEM1,Valid_PileTally_def,Valid_PileTally_def,
        Logical_list_MEM_VICE_VERCA_TheFunctional,eqe_list_dec2_verified]
      >> metis_tac[ALL_NON_EMPTY_def,Functional_AllNonEmpty_to_Logical,GET_CAND_PILE_MEM,
         EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
         Valid_PileTally_def,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional,
         eqe_list_dec2_verified]) 
     >- (match_mp_tac update_cand_pile_act_side
      >> metis_tac[ELECT_Auxiliary_dec_def,ALL_NON_EMPTY_def,ALL_NON_ZERO_def,
         Functional_AllNonEmpty_to_Logical,
         GET_CAND_PILE_MEM,Functional_AllNonEmpty_to_Logical,GET_CAND_PILE_MEM,
         EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
         Valid_PileTally_def,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional,
         eqe_list_dec2_verified,EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,
         PileTally_to_PileTally_DEC2,Valid_PileTally_def,Valid_PileTally_def,
         Logical_list_MEM_VICE_VERCA_TheFunctional,eqe_list_dec2_verified])) |> update_precondition;
 



(*
val r = translate update_cand_trans_val_def;
val r = translate update_cand_pile_def;


val r = translate ELECT_dec_def;


val update_cand_trans_val_side_def = fetch"-""update_cand_trans_val_side_def";
val update_cand_pile_side_def = fetch"-""update_cand_pile_side_def";
val elect_dec_side_def = fetch"-""elect_dec_side_def";


val update_cand_pile_side = Q.prove(
  `∀c a b d e.
    EVERY(λx. get_cand_tally x b ≠ 0) c ⇒
    update_cand_pile_side a b c d e`,
  Induct
  \\ rw[Once update_cand_pile_side_def,update_cand_trans_val_side_def]);

val elect_dec_side = Q.prove(
  `elect_dec_side a b c = T`,
  rw[definition"elect_dec_side_def"]
  \\ match_mp_tac update_cand_pile_side
  \\ fs[ELECT_Auxiliary_dec_def]
  \\ fs[bigger_than_quota_def,EVERY_MEM]
  \\ rw[] \\ res_tac
  \\ strip_tac \\ fs[]
  \\ imp_res_tac ratTheory.RAT_LES_LEQ_TRANS
  \\ fs[]) |> update_precondition;
*)

val r = translate Initial_Judgement_dec_def;

val r = translate Valid_Step_def;


val _ = export_theory();
