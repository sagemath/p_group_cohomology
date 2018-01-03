#~ Copyright 2018: Simon King <simon.king@uni-jena.de>
#
#~     This file is part of p_group_cohomology.
#
#~     p_group_cohomoloy is free software: you can redistribute it and/or modify
#~     it under the terms of the GNU General Public License as published by
#~     the Free Software Foundation, either version 2 of the License, or
#~     (at your option) any later version.
#
#~     p_group_cohomoloy is distributed in the hope that it will be useful,
#~     but WITHOUT ANY WARRANTY; without even the implied warranty of
#~     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#~     GNU General Public License for more details.
#
#~     You should have received a copy of the GNU General Public License
#~     along with p_group_cohomoloy.  If not, see <http://www.gnu.org/licenses/>.

ACLOCAL_AMFLAGS = -I m4
SUBDIRS = src

dbdir           = $(datadir)/pGroupCohomology
dist_db_DATA    = group_cohomology_database.tar

install-data-hook:
	cd $(DESTDIR)$(dbdir) && tar xf $(dist_db_DATA) && rm $(dist_db_DATA)

uninstall-hook:
	rm -r $(DESTDIR)$(dbdir)
