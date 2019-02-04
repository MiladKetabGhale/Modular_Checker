# Modular_Checker
This Repository consists of a framework for modular formalisation, verification and synthesis of verified certificate checkers for computation based on STV family of algorithms.


Table of Contents :

1. Dependencies of the framework
2. How to make executable verifiers?
3. The Architecture of the framework
4. How to extedn the framework?


1. This framework is formalised and verified in the theorem prover HOL4. Synthesis of executable verifiers proceeds with the verified compiler CakeML. Therefore one needs to first install HOL4 and then CakeML in your system.

One may find instructions for installation of the aforementioned in ;

                       https://github.com/CakeML/cakeml/blob/master/build-instructions.sh 


2. We formalise, verify, and provide synthesis of five different instances of verifiers each working for a different STV algorithm. 

2.1 ACT_STV : In order to generate a verifier for the STV algorithm used in the ACT state of Australia for the lower house elections, follow the instructions below.

  2.1.1 Go to the compilation directory and run the command make clean. Then run the command make compile_act. Doing so starts synthesis process of the ACT verifier. Note that linking and compiling takes a long time. If you had not previously built CakeML dependencies, it will begin from this point which itself takes hours (on a Core-i7 256, SSD 8gb Ram, takes six hours). Once CakeML dependencies are build, it automatically strats to synthesis the verifier which takes about 1.5 hours. 

  2.1.2 Once the preceeding step is finished, in the same directory run the commnad make act_move. Then go to the Executables directory. The verifier of ACT is now in the ACT_Exe sub-directory of the Executables.

2.2 Victoria_STV : To synthesise a verifier for the STV used in the upper house elections in Victoria state of Australia, follow the instructions below. 

  2.2.1 go to the compilation directory and run the command make clean. Then run make compile_victoria. 
  2.2.2 Once the above step is over, run make victoria_move. Under the Victoria_Exe subdirectory of the Executables directory you can find the Victoria verifier.


2.3 Union_STV : To synthesise a verifier for the STV used in several union elections in Australia such as ANU and Melbourne student unions, follow the instructions below. 

  2.3.1 go to the compilation directory and run the command make clean. Then run make compile_union.
  2.3.2 Once the above step is over, run make union_move. Under the Union_Exe subdirectory of the Executables directory
you can find the Union verifier.


2.4 CADE_STV : To synthesise a verifier for the STV used for electing the board of trustees in CADE conference, follow the instructions below. 

  2.4.1 go to the compilation directory and run the command make clean. Then run make compile_cade.
  2.4.2 Once the above step is over, run make cade_move. Under the CADE_Exe subdirectory of the Executables directory
you can find the CADE verifier.


2.5 ACT_STV_Variant : To synthesise a verifier for a variant of the  STV used in the lower house elections of the ACT state of Australia, follow the instructions below. 

  2.5.1 go to the compilation directory and run the command make clean. Then run make compile_actVar.
  2.5.2 Once the above step is over, run make actVar_move. Under the ACtvar_Exe subdirectory of the Executables directory
you can find the ACT_STV_Variant verifier.


3. There is a thorough explanation of the framework and its architecture in the following;
          
               https://github.com/MiladKetabGhale/FormaliSEConfPaper

However, here we shortly explain what the modules are and what their functions is. 

3.1 Auxiliary : This module consists of the framework base. It is comprised of seven submodules;
 
  3.1.1 AuxSpecScript.sml : this submodule contains formal specification of the components which are later used to specify what a verifier is.

  3.1.2 AuxIMPScript.sml : This submodule contains definition of computational implementations that are later proven correct with respect to thier specifications in the AuxSpec.

  3.1.3 AuxEquivProofsScript.sml : Formal proofs of match between declarations in AuxSpec and implemenations in AuxIMP happen in this submodule.

  3.2.4 AuxRulesSpecScript.sml : Formal specification of the generic STV as an abstract machine are carried out here.

  3.2.5 AuxRulesIMPScript.sml : Implementation of the generic STV machine happens in this module.

  3.2.6 AuxRulesEquivProofsScript.sml : Proofs of match between the specificatio and implementation of the machine proceeds here.

  3.2.7 AuxTransProgScript.sml : Translation of the implementations form HOL4 to CakeML equivalent implementations happen in this submodule.

3.2 Instantiation modules : There are modules for instantiating the generic STV machine to obtain specific versions of the machine used to synthesise a verifier from. These modules are called instantiations. Currently there are five instantiation modules, namely ACT_STV, Victoria_STV, Union_STV, CADE_STV and ACT_STV_Variant. In each of these modules one finds three submodules.

  3.2.1 RulesSpecScript.sml : Specification of the machine instantiation with a particular STV algorithm happens here.

  3.2.2 RulesIMPScript.sml : Implementation of the machine instantiation proceeds here.

  3.2.3 RulesTransProgScript.sml : Translation of instantiations into CakeML equivalent functions happen here.

3.3 Proofs : We automate proofs of match between specification of an instantiation with its implementation in this module. 

3.4 Checker : this module has four components.

  3.4.1 CheckerSpecScript.sml : specification of evidence verifier happens here. 

  3.4.2 CheckerIMPScript.sml : Implemenation of evidence verifier proceeds here. 

  3.4.3 CheckerProofsScript.sml : Proofs of match between verifier specification and implementation happens here.

  3.4.4 CheckerProgScript.sml : Translation of the verifier implementation into CakeML occurs here.

3.5 DeepSpec : Deep end-to-end specifications and verifications about the parser and verifier and thier interaction with the operating system happen here. 

3.6 compilation : Instantiation of the CakeML compiler for synthesis of provably correct verifiers happens here. In the proofs submodule, we establish proofs that executable verifiers behave in accordance with their properties in DeepSpec module.

3.7 Executables : after compilation, we send the executable verifier of each STV algorithm to a directory named accordingly. 

 
