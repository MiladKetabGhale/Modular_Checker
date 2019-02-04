clean :
	rm -rf *Theory* .hollogs .HOLMK ../Tempo/*Theory ../Tempo/.hollogs ../Tempo/.HOLMK ../Checker/*Theory* ../Checker/.hollogs ../Checker/.HOLMK ../Parser/*Theory* ../Parser/.hollogs ../Parser/.HOLMK  ../CheckerTrans/*Theory* ../CheckerTrans/.hollogs ../CheckerTrans/.HOLMK  ../Proofs/*Theory* ../Proofs/.hollogs ../Proofs/.HOLMK ../ACT_STV/*Theory* ../ACT_STV/.hollogs ../ACT_STV/.HOLMK ../Victoria_STV/*Theory* ../Victoria_STV/.hollogs ../Victoria_STV/.HOLMK  ../Union_STV/*Theory* ../Union_STV/.hollogs ../Union_STV/.HOLMK  ../ACT_STV_Variant/*Theory* ../ACT_STV_Variant/.hollogs ../ACT_STV_Variant/.HOLMK ../Auxiliary/*Theory* ../Auxiliary/.hollogs ../Auxiliary/.HOLMK proofs/*Theory* proofs/.hollogs proofs/.HOLMK ../CADE_STV/*Theory* ../CADE_STV/.HOLMK ../CADE_STV/.hollogs ../DeepSpec/.HOLMK ../DeepSpec/.hollogs ../DeepSpec/*Theory*  

check_count : check_count.o basis_ffi.o

depend_act : 
	cp ../Proofs/Holmakefile_ACT ../Proofs/Holmakefile

move_act :
	mv ./check_count ../Executables/ACT_Exe;
	mv ./basis_ffi.c ../Executables/ACT_Exe;
	mv ./basis_ffi.o ../Executables/ACT_Exe

depend_vic :
	cp ../Proofs/Holmakefile_Victoria ../Proofs/Holmakefile

move_vic : 
	mv ./check_count ../Executables/Victoria_Exe;
	mv ./basis_ffi.c ../Executables/Victoria_Exe;
	mv ./basis_ffi.o ../Executables/Victoria_Exe

depend_cade :	
	cp ../Proofs/Holmakefile_CADE ../Proofs/Holmakefile

move_cade :	
	mv ./check_count ../Executables/CADE_Exe;
	mv ./basis_ffi.c ../Executables/CADE_Exe;
	mv ./basis_ffi.o ../Executables/CADE_Exe

depend_union:
	cp ../Proofs/Holmakefile_Union ../Proofs/Holmakefile

move_union :	
	mv ./check_count ../Executables/Union_Exe;
	mv ./basis_ffi.c ../Executables/Union_Exe;
	mv ./basis_ffi.o ../Executables/Union_Exe

depend_actVar:
	cp ../Proofs/Holmakefile_Actvar ../Proofs/Holmakefile

move_actVar :
	mv ./check_count ../Executables/ACTvar_Exe;
	mv ./basis_ffi.c ../Executables/ACTvar_Exe;
	mv ./basis_ffi.o ../Executables/ACTvar_Exe

