ACLOCAL_AMFLAGS = -I m4
SUBDIRS = src

dbdir           = $(datadir)/pGroupCohomology
dist_db_DATA    = group_cohomology_database.tar

install-data-hook:
	cd $(DESTDIR)$(dbdir) && tar xf $(dist_db_DATA) && rm $(dist_db_DATA)

uninstall-hook:
	rm -r $(DESTDIR)$(dbdir)
