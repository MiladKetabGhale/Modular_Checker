open preamble 
     AuxSpecTheory
     AuxBoolTheory
     AuxEquivProofsTheory
     AuxRulesSpecTheory
     AuxRulesBoolTheory
     AuxRulesEquivProofsTheory
     ActRulesSpecTheory
    

val _ = new_theory "ActCheckerSpec"


val initial_judgement_def = Define `
   initial_judgement (l: cand list) j =
     ? ba t p bl bl2 e h.
     (j = NonFinal (ba, t, p, bl, bl2, e, h))
     /\ (!c. MEM c (MAP SND t) ==> (c = 0))
     /\ (!c. MEM c (MAP SND p) ==> (c = []))
     /\ (bl = [])
     /\ (bl2 = [])
     /\ (e = [])
     /\ (h = l)`;


val valid_judgements_def =  Define `
 valid_judgements params J ⇔
   (J <> []) /\ (∃w. LAST J = Final w)
   /\ (! J0 J1 j0 j1.
         (J = J0 ++ [j0;j1]++ J1) ==>
           ((HWIN params j0 j1)
           \/ (EWIN params j0 j1)
           \/ (COUNT params j0 j1)
           \/ (TRANSFER params j0 j1)
           \/ (ELECT params j0 j1)
           \/ (?c. MEM c (SND(SND params)) /\ ELIM_CAND c params j0 j1)
           \/ (TRANSFER_EXCLUDED params j0 j1)))`;
  
 
val Valid_Step_Spec_def = Define `
 Valid_Step_Spec params j0 j1 = 
          ((HWIN params j0 j1)
           \/ (EWIN params j0 j1)
           \/ (COUNT params j0 j1)
           \/ (TRANSFER params j0 j1)
           \/ (ELECT params j0 j1)
           \/ (?c. MEM c (SND(SND params)) /\ ELIM_CAND c params j0 j1)
           \/ (TRANSFER_EXCLUDED params j0 j1))`;
    
val Valid_intermediate_judgements_def = Define `
 Valid_intermediate_judgements params J = 
  ((J <> []) /\ (?w. LAST J = Final w)
  /\ (! J0 J1 j0 j1.
       (J = J0 ++ [j0;j1] ++ J1) ==> Valid_Step_Spec params j0 j1))`;
   
val Valid_Certificate_def = Define `
  (Valid_Certificate params [] ⇔ F) /\
  (Valid_Certificate params (first_judgement::rest_judgements) ⇔
     initial_judgement (SND(SND params)) first_judgement /\
     Valid_intermediate_judgements params (first_judgement::rest_judgements))`;


val _ = export_theory ();
