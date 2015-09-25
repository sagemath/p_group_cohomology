#CC=gcc # this is set by sage-env
ROOT=$(PWD)
OO="-O2"

.PHONY : all
all    : 
	#Cleaning up from previous builds
	$(MAKE) clean ROOTDIR=$(ROOT) -f $(ROOT)/mtx2.2.4/Makefile
	(cd $(ROOT)/bin/; $(MAKE) clean ROOTDIR=$(ROOT) -f $(ROOT)/present/Makefile)

	# Building MeatAxe
	$(MAKE) OO=$(OO) ROOTDIR=$(ROOT) -f $(ROOT)/mtx2.2.4/Makefile

	# Building David Green's binaries
	(cd $(ROOT)/bin/; $(MAKE) OO=$(OO) ROOTDIR=$(ROOT) -f $(ROOT)/present/Makefile)

clean	:
	$(MAKE) clean ROOTDIR=$(ROOT) -f $(ROOT)/mtx2.2.4/Makefile
	(cd $(ROOT)/bin/; $(MAKE) clean ROOTDIR=$(ROOT) -f $(ROOT)/present/Makefile)

install	:
	$(CP) $(ROOT)/lib/libmtx.a $(SAGE_LOCAL)/lib/
	# Copy the MeatAxe executables that we need
	$(CP) $(ROOT)/bin/zcv $(ROOT)/bin/zpr $(SAGE_LOCAL)/bin/
	# Copy David Green's executables
	$(CP) $(ROOT)/bin/makeActionMatrices $(ROOT)/bin/writeGroebnerBasis $(ROOT)/bin/makeNontips $(ROOT)/bin/groupInfo $(ROOT)/bin/perm2Gap $(ROOT)/bin/matmag $(ROOT)/bin/makeInclusionMatrix $(SAGE_LOCAL)/bin/
