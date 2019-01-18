open preamble  basis
     AuxSpecTheory
     AuxIMPTheory
     AuxEquivProofsTheory
     AuxRulesIMPTheory
     AuxRulesTransProgTheory
     RulesIMPTheory  
     
  
val _ = new_theory "RulesTransProg";

val _ = translation_extends"AuxRulesTransProg";
    
 
val () = use_mem_intro := true;
  
val r = translate ELIM_CAND_dec_def;   
 
val r = translate COUNT_dec_def;  
  
val r = translate TRANSFER_dec_def;
      
val r = translate TRANSFER_EXCLUDED_dec_def;
  
val () = use_mem_intro := false;

val r = translate HWIN_dec_def;
val r = translate EWIN_dec_def;
 
val r = translate ACT_TransValue_def;
val r = translate update_cand_transVal_ACT_def;
val r = translate update_cand_pile_ACT_def;

val r = translate ELECT_dec_def;
 
val transfer_dec_side_def = fetch"-""transfer_dec_side_def";
  
val transfer_dec_side = Q.prove(
  `transfer_dec_side a b c = T`,
  rw[definition"transfer_dec_side_def"]
  >> fs[NULL,NULL_EQ]) |> update_precondition;
  

val act_transvalue_side_def = fetch"-""act_transvalue_side_def";

val update_cand_transval_act_side_def = fetch"-""update_cand_transval_act_side_def";
val update_cand_pile_act_side_def = fetch"-""update_cand_pile_act_side_def";
val elect_dec_side_def = fetch"-""elect_dec_side_def";  
   
  
val act_transvalue_side = Q.prove(
 `! v4 v6 v5 v3. (get_cand_pile v3 v4 <> [])
          ==> act_transvalue_side v4 v6 v5 v3`,
   rw[act_transvalue_side_def]) |> update_precondition;
    
  
val update_cand_transval_act_side = Q.prove(
 `! v4 v2 v5 v3. (get_cand_pile v2 v3 <> [])
                  ==> update_cand_transval_act_side v4 v2 v5 v3`,
   rw[update_cand_transval_act_side_def] 
    >> rw[act_transvalue_side])|> update_precondition;


val update_cand_pile_act_side = Q.prove(
 `! a0 a1 a2 a3 a4.
  EVERY(\x. (get_cand_pile x a3 <> [])) a2 /\ EVERY(\x. (get_cand_pile x a4 <> [])) a2
       ==> update_cand_pile_act_side a0 a1 a2 a3 a4`,

         Induct_on `a2`
  \\ rw[Once update_cand_pile_act_side_def,update_cand_transval_act_side_def]
    \\ rw[act_transvalue_side_def]) |> update_precondition;

 
val elect_dec_side = Q.prove(
  `elect_dec_side a b c = T`,
  rw[definition"elect_dec_side_def"] 
     >> match_mp_tac update_cand_pile_act_side  
      >> metis_tac[ELECT_Auxiliary_dec_def,ALL_NON_EMPTY_def,
         Functional_AllNonEmpty_to_Logical,
         GET_CAND_PILE_MEM,Functional_AllNonEmpty_to_Logical,GET_CAND_PILE_MEM,
         EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,PileTally_to_PileTally_DEC2,
         Valid_PileTally_def,Valid_PileTally_def,Logical_list_MEM_VICE_VERCA_TheFunctional,
         eqe_list_dec2_verified,EVERY_CAND_HAS_ONE_PILE,PileTally_to_PileTally_DEC1,
         PileTally_to_PileTally_DEC2,Valid_PileTally_def,Valid_PileTally_def,
         Logical_list_MEM_VICE_VERCA_TheFunctional,eqe_list_dec2_verified]) |> update_precondition; 
 



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




val _ = export_theory();
