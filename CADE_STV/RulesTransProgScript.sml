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
 
val r = translate ELECT_dec_def;
 
val _ = export_theory()
