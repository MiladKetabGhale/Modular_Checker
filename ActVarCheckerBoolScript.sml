open preamble
     AuxSpecTheory
     AuxBoolTheory
     AuxEquivProofsTheory
     AuxRulesSpecTheory
     AuxRulesBoolTheory
     AuxRulesEquivProofsTheory
     ActVarRulesBoolTheory


val _ = new_theory "ActVarCheckerBool";


val Initial_Judgement_dec_def = Define `
        (Initial_Judgement_dec _ (Final _) ⇔ F)
     /\ (Initial_Judgement_dec l (NonFinal (ba, t, p, bl, bl2, e, h)) ⇔
                                (EVERY ((=) 0) (MAP SND t))
                             /\ (bl = [])
                             /\ (bl2 = [])
                             /\ (e = [])
                             /\ (h = l)
                             /\ (EVERY NULL (MAP SND p)))`;


val Valid_Step_def = Define`
  Valid_Step params j0 j1 ⇔
       HWIN_dec params j0 j1
    \/ EWIN_dec params j0 j1
    \/ COUNT_dec params j0 j1
    \/ TRANSFER_dec params j0 j1
    \/ ELECT_dec params j0 j1
    \/ EXISTS (λc. ELIM_CAND_dec c params j0 j1) (SND(SND params))
    \/ TRANSFER_EXCLUDED_dec params j0 j1`;


val valid_judgements_dec_def = Define `
       (valid_judgements_dec _ [] ⇔ F)
    /\ (valid_judgements_dec _ [Final _] ⇔ T)
    /\ (valid_judgements_dec _ [_] ⇔ F)
    /\ (valid_judgements_dec params (j0::j1::js) ⇔
        Valid_Step params j0 j1
        /\ (valid_judgements_dec params (j1::js)))`;


val valid_judgements_dec_ind = theorem"valid_judgements_dec_ind";


val valid_judgements_dec_LRC = Q.store_thm("valid_judgements_dec_LRC",
  `∀params ls.
    valid_judgements_dec params ls ⇔
    ∃s ls0 w. (ls = ls0 ++ [Final w]) ∧
      LRC (Valid_Step params) ls0 s (Final w)`,
  recInduct valid_judgements_dec_ind
  \\ rw[valid_judgements_dec_def,LRC_def]
  \\ Q.ISPEC_THEN`js`STRUCT_CASES_TAC SNOC_CASES
  \\ fs[SNOC_APPEND,LRC_def]
  \\ metis_tac[]);

val Check_Parsed_Certificate_def = Define`
  (Check_Parsed_Certificate params [] ⇔ F) /\
  (Check_Parsed_Certificate params(first_judgement::rest_judgements) ⇔
     Initial_Judgement_dec (SND(SND params)) first_judgement /\
     valid_judgements_dec params (first_judgement::rest_judgements))`;

val Check_Parsed_Certificate_LRC = Q.store_thm("Check_Parsed_Certificate_LRC",
  `Check_Parsed_Certificate params js ⇔
   ∃j0 ints w.
     (js = [j0] ++ ints ++ [Final w]) ∧
     LRC (Valid_Step params) (j0::ints) j0 (Final w) ∧
     Initial_Judgement_dec (SND(SND params)) j0`,
  Cases_on`js`
  \\ rw[Check_Parsed_Certificate_def,LRC_def,Initial_Judgement_dec_def,PULL_EXISTS,valid_judgements_dec_LRC]
  \\ rw[EQ_IMP_THM] \\ rw[LRC_def]
  >- (
    Cases_on`ls0` \\ fs[LRC_def,Initial_Judgement_dec_def]
    \\ metis_tac[] )
  \\ metis_tac[]);



val _ = export_theory ();

