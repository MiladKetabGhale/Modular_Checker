open preamble basis AuxSpecTheory RulesIMPTheory RulesTransProgTheory CheckerIMPTheory

val _ = new_theory"CheckerTransProg";

val _ = translation_extends"RulesTransProg";



val _ = export_theory()
