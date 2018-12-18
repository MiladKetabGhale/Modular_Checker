open preamble basis 
     AuxSpecTheory 
     AuxIMPTheory
     AuxEquivProofsTheory
     RulesIMPTheory 
     AuxRulesIMPTheory
     AuxRulesEquivProofsTheory
     AuxRulesTransProgTheory 
   
val _ = new_theory"RulesTransProg";

 

val _ = translation_extends"AuxRulesTransProg";
 


val () = use_mem_intro := true;


val r = translate ELIM_CAND_dec_def;
 
val r = translate COUNT_dec_def;

val r = translate TRANSFER_dec_def;


val r = translate TRANSFER_EXCLUDED_dec_def;
 
val () = use_mem_intro := false;
 
val r = translate HWIN_dec_def;
val r = translate EWIN_dec_def;


val r = translate update_cand_trans_val_def;
val r = translate update_cand_pile_def;

 
val update_cand_trans_val_side_def = fetch"-""update_cand_trans_val_side_def";
val update_cand_pile_side_def = fetch"-""update_cand_pile_side_def";
 
val update_cand_pile_side = Q.prove(
  `∀c a b d e.
    EVERY(λx. get_cand_tally x b ≠ 0) c ⇒
    update_cand_pile_side a b c d e`,
  Induct
  \\ rw[Once update_cand_pile_side_def,update_cand_trans_val_side_def]) |> update_precondition;
 
val r = translate ELECT_dec_def;

val elect_dec_side_def = fetch"-""elect_dec_side_def";
  
val elect_dec_side = Q.prove(
 `elect_dec_side a b c = T`,
  rw[definition"elect_dec_side_def"]
    >> match_mp_tac update_cand_pile_side
    >> rfs[ELECT_Auxiliary_dec_def]
    >> fs[bigger_than_quota_def,EVERY_MEM]
    >> rw[]
    >> res_tac
    >> strip_tac
    >> fs[]
    >> imp_res_tac ratTheory.RAT_LES_LEQ_TRANS
    >> fs[]) |> update_precondition;
 
 
val _ = export_theory()
