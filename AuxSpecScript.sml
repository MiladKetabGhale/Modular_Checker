open preamble

val _ = new_theory "AuxSpec";
  
(* Helper functions that have nothing to do with vote counting *)
(* Sum a list of rational numbers *)
val SUM_RAT_def = Define`
  SUM_RAT [] = (0:rat) /\
  SUM_RAT (h::t) = h + SUM_RAT t`;
(* -- *)
 
(* The main datatypes *)

(* A candidate is represented by a CakeML string *)
val _ = Datatype`cand = Cand mlstring`;
 
(* N.B. A more idiomatic approach might be to use records rather than tuples *)
 
val _ = type_abbrev("ballots",``:(((cand list) # rat) list)``);
val _ = type_abbrev("tallies",``:(cand,rat) alist``); 
val _ = type_abbrev("piles",``:(cand # ((((cand list) # rat) list) list)) list``);
      
(* A judgement is a state in the application of the vote counting rules.
   It is either a NonFinal state or a Final state.
*)
val _ = Datatype `
  judgement =
    NonFinal (
     (* ballots    *)               ballots #
     (* tallies    *)               tallies #
     (* piles      *)               piles #
     (* backlog of elected   *)     (cand list) #
     (* backlog of removed *)       (cand list) #
     (* elected    *)               (cand list) #
     (* continuing *)               (cand list) )
  | Final
    (* winners *) (cand list)`;


(* The rules *)

(* Each of rule corresponds to a step of vote counting
   A rule is of the following form:
   RULE (qu,st,l) j1 j2
   where
     (parameters of the election)
       qu is the quota (least amount of vote necessary to be elected)
       st is the number of seats
       l  is the list of initial candidates
     (transition step)
       j1 is the judgement before the rule application
       j2 is the judgement after the rule application
*)

val _ = type_abbrev("params",``:rat # num # (cand list)``);
  

val get_cand_tally_def = Define `
  get_cand_tally (c:cand) (ls:tallies) =
    case ALOOKUP ls c of NONE => -1 | SOME r => r`;
 
val get_cand_pile_def = Define `
  get_cand_pile (c:cand) (ls:piles) =
    case ALOOKUP ls c of NONE => [] | SOME r => r`;

val empty_cand_pile_def = Define `
   (empty_cand_pile (c:cand) ([]:piles) = []) /\
   (empty_cand_pile c (h::t) =
      if (c = FST h) then ((c, []) :: t)
      else h :: (empty_cand_pile c t))`;

 
val Valid_Init_CandList = Define `
  Valid_Init_CandList (l: cand list) = ((l <> []) /\ ALL_DISTINCT l) `;
 
val Valid_PileTally = Define `
  Valid_PileTally t (l: cand list) = (!c. (MEM c l) <=> (MEM c (MAP FST t))) `;

(* this function checks if the piles p1 and p2 are equal except for candidate c where
   (c,[]) belongs to p2 but not necessarily to p1.
*)
val subpile1_def = Define `
  subpile1 c (p1:piles) p2 ⇔
    EVERY (λp. MEM (if c = FST p then (c,[]) else p) p2) p1`;
 
(* this function checks if candidate c appears as a first component in both ps and p1 and
   also checks if all of the other members of ps belong to p1
*)
val subpile2_def = Define`
  subpile2 c (ps:piles) p1 ⇔
    EVERY (λp. if c = FST p then T else MEM p p1) ps`; 
 
val equal_except_def = Define `
 ((equal_except (c: cand) l nl ) =
   ?l1 l2.
     (l = l1 ++ l2)
     /\ (nl = l1 ++ [c] ++ l2)
     /\ (~ (MEM c l1))
     /\ (~ (MEM c l2))) `; 

val get_cand_pile_list_def = Define `
  (get_cand_pile_list ([]: cand list) (ls: piles) = []) /\
    (get_cand_pile_list (l0::l1) ls = (case ALOOKUP ls l0 of NONE =>
              (get_cand_pile_list l1 ls) | SOME r => (r ++ (get_cand_pile_list l1 ls)))) `;

 
val first_continuing_cand_def = Define `
   first_continuing_cand (c: cand) (b: cand list)  (h: cand list) =
      (?l1 l2. (b = l1 ++ c::l2) /\ (!d. MEM d l1 ==> ~ MEM d h))`;
   
 
val tally_comparison_def = Define `
  tally_comparison (t:tallies) c1 c2 ⇔ (get_cand_tally c2 t <= get_cand_tally c1 t)`;
 
(*the Gregorian method for updating transfer value*)
val update_cand_trans_val_def = Define `
    (update_cand_trans_val (qu:rat) (c:cand) (t:tallies) (p: ((cand list) # rat) list) =
        MAP (λr. r * (((get_cand_tally c t) - qu) / (get_cand_tally c t)))
          (MAP SND (p)))`; 

val _ = export_theory();
 
