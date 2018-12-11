# Modular_Checker
This Repository consists of a modular framework for formalisation, verification and synthesis of verified certificate checkers for computation based on STV algorithms.


About the Content of the repository: 



1. Base files which consist themselves are of three types. AuxSpecScript.sml comprises the specification of many auxiliary declarations which are then used in formalisation of various checkers for different STV algorithms. The file AuxBoolScript.sml contains the boolean functions which are ment to be the computational realisation of the specifications in AuxSpecScript.sml. Finally AuxEquivProofsScript.sml includes formal proofs of the correspondence between the specifications in AuxSpec with their computational boolean counterparts in AuxBool.

2. Another group of files deal with formalisation and verification of auxiliary declarations and functions used to abstract proofs and definitions of a significant part of counting rules. The file AuxRulesSpecScript.sml consists of HOL assertions which encapsulate the common properties expacted from any correct certificate of an STV scheme to satisfy. These properties shared by STV schemes are defined once and for all in AuxRulesScript.sml. There are boolean valued counterparts for each of the assertions in AuxRulesSpec. These computational functions are placed in AuxRulesBoolScript.sml. Finally, AuxRulesProofs consists of proofs of equivalences between declarations in AuxRulesSpec with functions in AuxRulesBool. 

3. There are files for specifying checkers for various STV schemes and defining  boolean valued checker functions for each STV algorithm, and proofs of match between checkers as HOL declaratoins with checkers as HOL boolean valued computational entities. These files are name by the following convention:
             
               <Abbrev for the STV formalised> ++ Checker ++ (Spec/Bool/Proofs) ++ Script.sml

For example the STV used in (some) student unions in Australian universities such as ANU, has a UnionCheckerSpecScript.sml meant as an specification of the Union_STV. Basically, such an specification happens by using the auxiliary declarations in AuxSpec and AuxRulesSpec. It also has UnionCheckerBoolScript.sml which is a boolean valued checker function in HOL. Finally, the file UnionCheckerProofsScript.sml comprises proofs that the boolean valued checker indeed satisfies the expectatons of its specification. 

4. There are files for translating HOL boolean valued functions mentioned above into CakeML functions. These files are named by the following convention :

                        <some abbrev> ++ ProgScript.sml

For example, the files ParserProgScript.sml contains translation of parser component into CakeML. 


About Some Specific Files ::

1. The file RulesProofsScript.sml consists of showing correspondence between the specification and boolean counting rules for all of our instances. This stands in a contrast with proofs in files named <STV_Name>RulesProofsScript.sml where each only deals with the same proofs for only the <STV_Name> rather than all STVs

     
