#CC=gcc # this is set by sage-env
ROOT=$(PWD)
OO="-O2"

.PHONY : all
all    :
	# Building David Green's binaries
	(cd $(ROOT)/bin/; $(MAKE) OO=$(OO) ROOTDIR=$(ROOT) -f $(ROOT)/present/Makefile)

clean	:
	(cd $(ROOT)/bin/; $(MAKE) clean ROOTDIR=$(ROOT) -f $(ROOT)/present/Makefile)

install	:
	# Copy David Green's executables
	$(CP) $(ROOT)/bin/makeActionMatrices $(ROOT)/bin/makeNontips $(ROOT)/bin/groupInfo $(ROOT)/bin/perm2Gap $(ROOT)/bin/matmag $(ROOT)/bin/makeInclusionMatrix $(SAGE_LOCAL)/bin/
