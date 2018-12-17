open preamble basis

open pegparserTheory

val _ = new_theory "cmlparse";

val _ = translation_extends "basisProg";

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)
  in def end

val _ = find_def_for_const := def_of_const;

val INTRO_FLOOKUP = Q.store_thm("INTRO_FLOOKUP",
  `(if n IN FDOM G.rules
     then pegexec$EV (G.rules ' n) i r y fk
     else Result xx) =
    (case FLOOKUP G.rules n of
       NONE => Result xx
     | SOME x => pegexec$EV x i r y fk)`,
  SRW_TAC [] [finite_mapTheory.FLOOKUP_DEF]);

val _ = translate (def_of_const ``coreloop``
                    |> REWRITE_RULE [INTRO_FLOOKUP]
                    |> SPEC_ALL |> RW1 [FUN_EQ_THM])

val CL_side = store_thm(
  "CL_side",
  ``(wfG x ∧ ∃i. y = pegexec$EV x.start i [] done failed) ⇒ coreloop_side x y``,
  simp[fetch "-" "coreloop_side_def", optionTheory.IS_SOME_EXISTS] >>
  strip_tac >>
  qmatch_abbrev_tac `(?r. f y = SOME r)` >>
  `f = coreloop x`
    by (simp[Abbr`f`, pegexecTheory.coreloop_def] >>
        simp[FUN_EQ_THM] >> gen_tac >> AP_THM_TAC >> AP_TERM_TAC >>
        simp[FUN_EQ_THM] >> gen_tac >>
        rename [‘evalcase_CASE ev’] >>
        Cases_on `ev` >> simp[]
        >- (rename [‘pegsym_CASE psym’] >>
            Cases_on `psym` >> simp[INTRO_FLOOKUP]) >>
        rename [‘kont_CASE kk’] >> Cases_on `kk` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  markerLib.UNABBREV_ALL_TAC >> rw[] >>
  Q.REFINE_EXISTS_TAC `Result r` >>
  irule pegexecTheory.coreloop_total >> simp[]);

val _ = translate pegexecTheory.peg_exec_def

val pe_side = Q.store_thm(
  "pe_side",
  ‘∀pg sym i opts k fk.
     wfG pg ∧ sym = pg.start ∧ opts = [] ∧ k = done ∧ fk = failed ⇒
     peg_exec_side pg sym i opts k fk’,
  simp[DB.fetch "-" "peg_exec_side_def", CL_side]);

val _ = translate pegparserTheory.parse_def

val parse_prog_side = Q.store_thm(
  "parse_prog_side",
  ‘∀x. parse_side x = T’,
  simp[DB.fetch "-" "parse_side_def"] >> gen_tac >> irule pe_side >>
  simp[PEG_wellformed] >> simp[jPEG_def]) |> update_precondition;

val _ = export_theory();
