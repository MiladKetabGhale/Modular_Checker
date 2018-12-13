open HolKernel Parse boolLib bossLib;

open pegTheory

val _ = new_theory "pegparser";

val _ = temp_type_abbrev ("ballot", “:char # rat”)
val _ = temp_type_abbrev ("pile", “:char # ballot list list”)
val _ = temp_type_abbrev ("judgement",
  ``:ballot list # ballot list # pile list # char list # char list #
     char list # char list``)

val _ = Datatype‘
  NTforms = Num num
          | Rat num num
          | Cand char
          | CandL (char list)
          | Ballot ballot  (* also tally *)
          | BallotL (ballot list)
          | BallotLL (ballot list list)
          | Pile pile
          | PileList (pile list)
          | Judgement judgement
          | Certificate rat num (char list) (char list) (judgement list)
          | Forms (NTforms list)
          | Error
’;


val tokP_def = Define‘tokP P = tok P (Cand o FST)’

val pegf_def = Define‘pegf sym f = seq sym (empty Error) (λe1 e2. f e1)’;

val lws_def = Define`
  lws t = seq (rpt (tokP isSpace) (λfl. Cand #"X")) t (λe1 e2. e2)
`;

val _ = Datatype`jNT = nNum | nRat | nCand | nQuota | nSeats | nCandidate
                       | nCandidateList | nBallot | nBallotList
                       | nBallotListList | nTally | nTallyList | nPile
                       | nPileList | nJudgement`;

val jnt_def = Define‘jnt (ntsym : jNT) = nt (INL ntsym) I’;

val NTF_to_num_def = Define‘
  (NTF_to_num (Cand c) = ORD c - ORD #"0") ∧
  (NTF_to_num (Num n) = n) ∧
  (NTF_to_num _ = 0n)
’;


val dsToNumExp_def = Define‘
  (dsToNumExp [] = Rat 0 1) ∧
  (dsToNumExp (f::fs) =
   case dsToNumExp fs of
       Rat n exp => Rat (NTF_to_num f * exp + n) (exp * 10))
’;

val pickleft_def = Define‘
  pickleft p1 p2 = seq p1 p2 (λe1 e2. e1)
’;
val _ = set_mapped_fixity {fixity = Infixl 500,
                           term_name = "pickleft",
                           tok = "↫"}
val pickright_def = Define‘
  pickright p1 p2 = seq p1 p2 (λe1 e2. e2)
’;
val _ = set_mapped_fixity {fixity = Infixl 500,
                           term_name = "pickright",
                           tok = "↬"};

val destCand_def = Define‘
  (destCand (Cand c) = c) ∧ (destCand _ = CHR 0)
’;

val destCandl_def = Define‘
  (destCandl (CandL cs) = cs) ∧ (destCandl _ = [])
’;

val CANDL_CONS_def = Define‘
  CANDL_CONS f1 f2 = CandL (destCand f1 :: destCandl f2)
’;

val destBallot_def = Define‘
  destBallot (Ballot t) = t ∧ destBallot _ = (CHR 0, 0)
’;

val destBallotL_def = Define‘
  destBallotL (BallotL l) = l ∧ destBallotL _ = []
’;

val BALLOTL_CONS_def = Define‘
  BALLOTL_CONS f1 f2 = BallotL (destBallot f1 :: destBallotL f2)
’;

val destBallotLL_def = Define‘
  destBallotLL (BallotLL bll) = bll ∧ destBallotLL _ = []
’;

val BALLOTLL_CONS_def = Define‘
  BALLOTLL_CONS bl bll = BallotLL (destBallotL bl :: destBallotLL bll)
’;

val CONS_NumRat_def = Define‘
  (CONS_NumRat f (Rat n exp) = Num (NTF_to_num f * exp + n)) ∧
  (CONS_NumRat f _ = Num (NTF_to_num f))
’;

val mkBallot_def = Define‘
  (mkBallot cf (Rat n d) = Ballot (destCand cf, rat_of_num n / rat_of_num d)) ∧
  (mkBallot _ _ = Error)
’;

val mkPile_def = Define‘
  mkPile cf (BallotLL bll) = Pile (destCand cf, bll) ∧
  mkPile _ _ = Error
’;

val destPile_def = Define‘
  destPile (Pile p) = p ∧ destPile _ = (CHR 0, [])
’;

val destPileList_def = Define‘
  destPileList (PileList pl) = pl ∧ destPileList _ = []
’;

val PILE_CONS_def = Define‘
  PILE_CONS pf psf = PileList (destPile pf :: destPileList psf)
’;

val destForms_def = Define‘
  destForms (Forms l) = l ∧ destForms _ = []
’;

val seql_def = Define‘
  seql [] = empty (Forms []) ∧
  seql (sym::rest) = seq sym (seql rest) (λf fs. Forms (f::destForms fs))
’;

val mkJudgement_def = Define‘
  mkJudgement (Forms [bl1_f; bl2_f; ps_f; cs1_f; cs2_f; cs3_f; cs4_f]) =
      Judgement (destBallotL bl1_f, destBallotL bl2_f, destPileList ps_f,
                 destCandl cs1_f, destCandl cs2_f,
                 destCandl cs3_f, destCandl cs4_f)
’;

val jPEG_def = zDefine ‘
  jPEG = <|
    start := jnt nJudgement ;
    rules := FEMPTY |++ [
      (INL nNum, seq (tokP isDigit)
                     (rpt (tokP isDigit) dsToNumExp)
                     CONS_NumRat);
      (INL nRat,
       (seq (jnt nNum ↫ tokP ((=) #"%")) (jnt nNum)
            (λf1 f2. Rat (NTF_to_num f1) (NTF_to_num f2))));
      (INL nQuota, jnt nRat);
      (INL nCandidateList,
       tokP ((=) #"[") ↬
       choice (tokP ((=) #"]"))
              (seq (tokP isAlpha)
                   (rpt (tokP ((=) #",") ↬ tokP isAlpha)
                        (CandL o MAP destCand))
                   CANDL_CONS ↫ tokP ((=) #"]"))
              (λs. case s of INL _ => CandL [] | INR cs => cs));
      (INL nBallot,
       seq (tokP ((=) #"(") ↬ tokP isAlpha)
           (tokP ((=) #",") ↬ jnt nRat ↫ tokP ((=) #")"))
           mkBallot);
      (INL nBallotList,
       tokP ((=) #"[") ↬
       choice (tokP ((=) #"]"))
              (seq (jnt nBallot)
                   (rpt (tokP ((=) #",") ↬ jnt nBallot)
                        (BallotL o MAP destBallot))
                   BALLOTL_CONS ↫ tokP ((=) #"]"))
              (λs. case s of INL _ => BallotL [] | INR cs => cs));
      (INL nBallotListList,
       tokP ((=) #"[") ↬
       choice (tokP ((=) #"]"))
              (seq (jnt nBallotList)
                   (rpt (tokP ((=) #",") ↬ jnt nBallotList)
                        (BallotLL o MAP destBallotL))
                   BALLOTLL_CONS ↫ tokP ((=) #"]"))
              (λs. case s of INL _ => BallotL [] | INR cs => cs));
      (INL nTally,
       seq (tokP isAlpha ↫ tokP ((=) #"{"))
           (jnt nRat ↫ tokP ((=) #"}")) mkBallot);
      (INL nTallyList,
       choice (seq (jnt nTally)
                   (rpt (tokP ((=) #" ") ↬ jnt nTally)
                        (BallotL o MAP destBallot))
                   BALLOTL_CONS)
              (empty (BallotL [])) (λs. case s of INL e => e | INR e => e));
      (INL nPile,
       seq (tokP isAlpha ↫ tokP ((=) #"{"))
           (jnt nBallotListList ↫ tokP ((=) #"}")) mkPile);
      (INL nPileList,
       choice (seq (jnt nPile)
                   (rpt (tokP ((=) #" ") ↬ jnt nPile)
                        (PileList o MAP destPile))
                   PILE_CONS)
              (empty (PileList [])) (λs. case s of INL e => e | INR e => e));
      (INL nJudgement,
       pegf (seql [
                jnt nBallotList ↫ tokP ((=) #";") ↫ tokP ((=) #" ");
                jnt nTallyList ↫ tokP ((=) #";") ↫ tokP ((=) #" ");
                jnt nPileList  ↫ tokP ((=) #";") ↫ tokP ((=) #" ");
                jnt nCandidateList ↫ tokP ((=) #";") ↫ tokP ((=) #" ");
                jnt nCandidateList ↫ tokP ((=) #";") ↫ tokP ((=) #" ");
                jnt nCandidateList ↫ tokP ((=) #";") ↫ tokP ((=) #" ");
                jnt nCandidateList
            ]) mkJudgement)

    ]
  |>
’;

val FDOM_jPEG = save_thm(
  "FDOM_jPEG",
  SIMP_CONV (srw_ss()) [jPEG_def,
                        finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
                        finite_mapTheory.DOMSUB_FUPDATE_THM,
                        finite_mapTheory.FUPDATE_LIST_THM]
            ``FDOM jPEG.rules``);

val spec0 =
    pegexecTheory.peg_nt_thm
      |> Q.GEN `G`  |> Q.ISPEC `jPEG`
      |> SIMP_RULE (srw_ss()) [FDOM_jPEG]
      |> Q.GEN `n`

fun mk_rule_app n =
  SIMP_CONV (srw_ss())
            [jPEG_def, finite_mapTheory.FUPDATE_LIST_THM,
             finite_mapTheory.FAPPLY_FUPDATE_THM]
            (mk_comb(``FAPPLY jPEG.rules``, n))

val jNTs = map (fn s => Parse.Term [QUOTE ("INL " ^ s ^ " : jNT inf")]) [
      "nBallot", "nQuota", "nRat", "nNum", "nCandidateList", "nBallotList",
      "nBallotListList", "nTally", "nTallyList", "nPile", "nPileList",
      "nJudgement"]

val jPEG_applied = save_thm(
  "jPEG_applied",
  LIST_CONJ (map mk_rule_app jNTs));

fun mkrule n = SIMP_RULE bool_ss [jPEG_applied] (SPEC n spec0)


val jpeg_exec_rules = save_thm(
  "jpeg_exec_rules",
  LIST_CONJ (map mkrule jNTs))

val _ = computeLib.add_persistent_funs ["jpeg_exec_rules"]

val loc0_def = Define`loc0 = Locs (locn 0 0 0) (locn 0 0 0)`;
val parse_def = Define‘
  parse s =
    case peg_exec jPEG (jnt nJudgement)
                  (MAP (λc. (c, loc0)) s) [] done failed
     of
        Result (SOME ([], e)) => SOME e
      | _ => NONE
’;

val wfpeg_rwts = wfpeg_cases
                   |> ISPEC ``jPEG``
                   |> (fn th => map (fn t => Q.SPEC t th)
                                    [`seq e1 e2 f`, `choice e1 e2 f`, `tok P f`,
                                     `any f`, `empty v`, `not e v`, `rpt e f`,
                                     `tokP t`, `s1 ↫ s2`, `s1 ↬ s2`
                      ])
                   |> map (CONV_RULE
                             (RAND_CONV (SIMP_CONV (srw_ss())
                                                   [tokP_def, jnt_def])))

val wfpeg_lnt = wfpeg_cases
                  |> ISPEC ``jPEG``
                  |> Q.SPEC `jnt n`
                  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [jnt_def]))

val peg0_rwts = peg0_cases
                  |> ISPEC ``jPEG`` |> CONJUNCTS
                  |> map (fn th => map (fn t => Q.SPEC t th)
                                       [`tok P f`, `choice e1 e2 f`,
                                        `seq e1 e2 f`, `lws p`, `rpt p f`,
                                        `pickleft e1 e2`, `pickright e1 e2`,
                                        `tokP t`, `empty l`])
                  |> List.concat
                  |> map (CONV_RULE
                            (RAND_CONV (SIMP_CONV (srw_ss())
                                           [tokP_def, lws_def,
                                            pickright_def, pickleft_def])))

fun peg0_nt t =
  let
    val th = Q.prove(
      ‘¬peg0 jPEG (jnt ^t)’,
      simp[jnt_def] >> simp[Once peg0_cases] >>
      simp(FDOM_jPEG :: jPEG_applied :: seql_def :: pegf_def :: peg0_rwts))
    val _ = augment_srw_ss [rewrites [th]]
  in
    th
  end

val topoNTs = [“nNum”, “nRat”, “nBallot”, “nCandidateList”, “nBallotList”,
                “nTally”, “nPile”, “nJudgement”]
val peg0_nts = save_thm("peg0_nts[simp]", LIST_CONJ (map peg0_nt topoNTs))

val wfpeg_jnt = wfpeg_cases
                  |> ISPEC ``jPEG``
                  |> Q.SPEC `jnt n`
                  |> CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss()) [jnt_def]))

fun wfnt(t,acc) =
  let
    val th =
        Q.prove(`wfpeg jPEG (jnt ^t)`,
          SIMP_TAC (srw_ss()) [jPEG_applied, wfpeg_jnt, FDOM_jPEG, pegf_def,
                               pickleft_def, pickright_def, seql_def] >>
          simp(peg0_nts :: peg0_rwts @ wfpeg_rwts @ acc))
in
  th::acc
end;

val wfnts = List.foldl wfnt []
                   (topoNTs @ [“nPileList”, “nTallyList”, “nBallotListList”])

val subexprs_jnt = Q.prove(
  `subexprs (jnt n) = {jnt n}`,
  simp[subexprs_def, jnt_def]);

val frange_image = Q.prove(
  `FRANGE fm = IMAGE (FAPPLY fm) (FDOM fm)`,
  simp[finite_mapTheory.FRANGE_DEF, pred_setTheory.EXTENSION] >> metis_tac[]);

val peg_start = SIMP_CONV(srw_ss()) [jPEG_def]``jPEG.start``

val peg_range =
    SIMP_CONV (srw_ss())
              [FDOM_jPEG, frange_image, jPEG_applied]
              ``FRANGE jPEG.rules``
val PEG_exprs = save_thm(
  "PEG_exprs",
  ``Gexprs jPEG``
    |> SIMP_CONV (srw_ss())
         [Gexprs_def, subexprs_def, peg_range,
          subexprs_jnt, peg_start,
          pred_setTheory.INSERT_UNION_EQ
         ])

val PEG_wellformed = Q.store_thm(
  "PEG_wellformed",
  `wfG jPEG`,
  simp[wfG_def, Gexprs_def, subexprs_def, seql_def,
       subexprs_jnt, peg_start, peg_range, DISJ_IMP_THM, FORALL_AND_THM,
       lws_def, tokP_def, pickright_def, pickleft_def, pegf_def] >>
  simp(peg0_nts :: wfpeg_rwts @ peg0_rwts @ wfnts));

(* test cases
EVAL ``parse "[(A,2%6),(B,3%5)]; A{2%4} B{3%5}; C{[[],[(C,10%13)]]}; [a,b,c]; []; [c,d]; [e]"``;
*)


val _ = export_theory();
