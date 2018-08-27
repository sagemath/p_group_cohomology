# -*- coding: utf-8 -*-
#
# "p_group_cohomology" documentation build configuration file, created by
# sphinx-quickstart on Wed Jan  3 00:48:45 2018.
#
# This file is execfile()d with the current directory set to its
# containing dir.
#
# Note that not all possible configuration values are present in this
# autogenerated file.
#
# All configuration values have a default; values that are commented out
# serve to show the default.

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
import os
import sys
from sage.env import SAGE_DOC_SRC, SAGE_DOC, SAGE_SRC, THEBE_DIR, SAGE_SHARE
COHO_DOC_SRC = os.path.abspath('../pGroupCohomology')

sys.path.insert(0, COHO_DOC_SRC)
sys.path.append(os.path.join(SAGE_SRC, "sage_setup", "docbuild", "ext"))


# -- General configuration ------------------------------------------------

# If your documentation needs a minimal Sphinx version, state it here.
#
# needs_sphinx = '1.0'

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = ['inventory_builder',
              'sage_autodoc',
              'sphinx.ext.intersphinx',
              'sphinx.ext.todo']

# The suffix(es) of source filenames.
# You can specify multiple suffix as a list of string:
#
# source_suffix = ['.rst', '.md']
source_suffix = '.rst'

# The master toctree document.
master_doc = 'index'

# General information about the project.
project = u'"p_group_cohomology"'
copyright = u'2018, "Simon King"'
author = u'"Simon King"'

# The version info for the project you're documenting, acts as replacement for
# |version| and |release|, also used in various other places throughout the
# built documents.
#
# The short X.Y version.
version = u'3.0.1'
# The full version, including alpha/beta/rc tags.
release = u'3.0.1'

# The language for content autogenerated by Sphinx. Refer to documentation
# for a list of supported languages.
#
# This is also used if you do content translation via gettext catalogs.
# Usually you set "language" from the command line for these cases.
language = None

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This patterns also effect to html_static_path and html_extra_path
exclude_patterns = []

default_role = 'math'

add_function_parentheses = True

add_module_names = True

# The name of the Pygments (syntax highlighting) style to use.
pygments_style = 'sphinx'

# If true, `todo` and `todoList` produce output, else they produce nothing.
todo_include_todos = True

# Cross-links to other project's online documentation.
intersphinx_mapping = {
    'python'  : ('https://docs.python.org/',
                 os.path.join(SAGE_DOC_SRC, "common", "python.inv")),
    'sagemath': ('http://doc.sagemath.org/',
                 os.path.join(SAGE_SHARE, "doc", "sage", "html", "en", "reference", "objects.inv"))
                }

## TODO: Automaticall generated inventory

pythonversion = sys.version.split(' ')[0]
# Python and Sage trac ticket shortcuts. For example, :trac:`7549` .

# Sage trac ticket shortcuts. For example, :trac:`7549` .
extlinks = {
    'python': ('https://docs.python.org/release/'+pythonversion+'/%s', ''),
    'trac': ('https://trac.sagemath.org/%s', 'trac ticket #'),
    'wikipedia': ('https://en.wikipedia.org/wiki/%s', 'Wikipedia article '),
    'arxiv': ('http://arxiv.org/abs/%s', 'Arxiv '),
    'oeis': ('https://oeis.org/%s', 'OEIS sequence '),
    'doi': ('https://dx.doi.org/%s', 'doi:'),
    'pari': ('http://pari.math.u-bordeaux.fr/dochtml/help/%s', 'pari:'),
    'mathscinet': ('http://www.ams.org/mathscinet-getitem?mr=%s', 'MathSciNet ')
    }


# -- Options for HTML output ----------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'classic'

# Theme options are theme-specific and customize the look and feel of a theme
# further.  For a list of options available for each theme, see the
# documentation.
#
html_theme_options = {}

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static', THEBE_DIR]
html_theme_path = [os.path.join(SAGE_DOC_SRC, 'common', 'themes')]

# Custom sidebar templates, must be a dictionary that maps document names
# to template names.
#
# This is required for the alabaster theme
# refs: http://alabaster.readthedocs.io/en/latest/installation.html#sidebars
#~ html_sidebars = {
    #~ '**': [
        #~ 'about.html',
        #~ 'navigation.html',
        #~ 'relations.html',  # needs 'show_related': True theme option to display
        #~ 'searchbox.html',
        #~ 'donate.html',
    #~ ]
#~ }

extensions.append('sphinx.ext.mathjax')
mathjax_path = 'MathJax.js?config=TeX-AMS_HTML-full,../mathjax_sage.js'

from sage.misc.latex_macros import sage_mathjax_macros
#~ html_theme_options['mathjax_macros'] = sage_mathjax_macros()

mathjax_relative = 'mathjax'

# It would be really nice if sphinx would copy the entire mathjax directory,
# (so we could have a _static/mathjax directory), rather than the contents of the directory

mathjax_static = os.path.join(SAGE_SHARE, mathjax_relative)
html_static_path.append(mathjax_static)
exclude_patterns += ['**/'+os.path.join(mathjax_relative, i)
                     for i in ('docs', 'README*', 'test',
                               'unpacked', 'LICENSE')]

# Add any paths that contain templates here, relative to this directory.
templates_path = [os.path.join(SAGE_DOC_SRC, 'common', 'templates'), '_templates']

#####################

modindex_common_prefix = ['pGroupCohomology.']

# By default document are not master.
multidocs_is_master = True

# -- Options for HTMLHelp output ------------------------------------------

# Output file base name for HTML help builder.
htmlhelp_basename = 'mod-pgroupcohomologydoc'


# -- Options for LaTeX output ---------------------------------------------

latex_elements = {
    # The paper size ('letterpaper' or 'a4paper').
    #
    # 'papersize': 'letterpaper',

    # The font size ('10pt', '11pt' or '12pt').
    #
    # 'pointsize': '10pt',

    # Additional stuff for the LaTeX preamble.
    #
    # 'preamble': '',

    # Latex figure (float) alignment
    #
    # 'figure_align': 'htbp',
}

# Grouping the document tree into LaTeX files. List of tuples
# (source start file, target name, title,
#  author, documentclass [howto, manual, or own class]).
latex_documents = [
    (master_doc, 'mod-pgroupcohomology.tex', u'"mod-p group cohomology" Documentation',
     u'"Simon King"', 'manual'),
]

latex_elements['preamble'] = r"""
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{textcomp}
\usepackage{mathrsfs}
\usepackage{iftex}

% Only declare unicode characters when compiling with pdftex; E.g. japanese
% tutorial does not use pdftex
\ifPDFTeX
    \DeclareUnicodeCharacter{01CE}{\capitalcaron a}
    \DeclareUnicodeCharacter{0428}{cyrillic Sha}
    \DeclareUnicodeCharacter{250C}{+}
    \DeclareUnicodeCharacter{2510}{+}
    \DeclareUnicodeCharacter{2514}{+}
    \DeclareUnicodeCharacter{2518}{+}
    \DeclareUnicodeCharacter{253C}{+}

    \DeclareUnicodeCharacter{03B1}{\ensuremath{\alpha}}
    \DeclareUnicodeCharacter{03B2}{\ensuremath{\beta}}
    \DeclareUnicodeCharacter{03B3}{\ensuremath{\gamma}}
    \DeclareUnicodeCharacter{0393}{\ensuremath{\Gamma}}
    \DeclareUnicodeCharacter{03B4}{\ensuremath{\delta}}
    \DeclareUnicodeCharacter{0394}{\ensuremath{\Delta}}
    \DeclareUnicodeCharacter{03B5}{\ensuremath{\varepsilon}}
    \DeclareUnicodeCharacter{03B6}{\ensuremath{\zeta}}
    \DeclareUnicodeCharacter{03B7}{\ensuremath{\eta}}
    \DeclareUnicodeCharacter{03B8}{\ensuremath{\vartheta}}
    \DeclareUnicodeCharacter{0398}{\ensuremath{\Theta}}
    \DeclareUnicodeCharacter{03BA}{\ensuremath{\kappa}}
    \DeclareUnicodeCharacter{03BB}{\ensuremath{\lambda}}
    \DeclareUnicodeCharacter{039B}{\ensuremath{\Lambda}}
    \DeclareUnicodeCharacter{00B5}{\ensuremath{\mu}}      % micron sign
    \DeclareUnicodeCharacter{03BC}{\ensuremath{\mu}}
    \DeclareUnicodeCharacter{03BD}{\ensuremath{\nu}}
    \DeclareUnicodeCharacter{03BE}{\ensuremath{\xi}}
    \DeclareUnicodeCharacter{039E}{\ensuremath{\Xi}}
    \DeclareUnicodeCharacter{03B9}{\ensuremath{\iota}}
    \DeclareUnicodeCharacter{03C0}{\ensuremath{\pi}}
    \DeclareUnicodeCharacter{03A0}{\ensuremath{\Pi}}
    \DeclareUnicodeCharacter{03C1}{\ensuremath{\rho}}
    \DeclareUnicodeCharacter{03C3}{\ensuremath{\sigma}}
    \DeclareUnicodeCharacter{03A3}{\ensuremath{\Sigma}}
    \DeclareUnicodeCharacter{03C4}{\ensuremath{\tau}}
    \DeclareUnicodeCharacter{03C6}{\ensuremath{\varphi}}
    \DeclareUnicodeCharacter{03A6}{\ensuremath{\Phi}}
    \DeclareUnicodeCharacter{03C7}{\ensuremath{\chi}}
    \DeclareUnicodeCharacter{03C8}{\ensuremath{\psi}}
    \DeclareUnicodeCharacter{03A8}{\ensuremath{\Psi}}
    \DeclareUnicodeCharacter{03C9}{\ensuremath{\omega}}
    \DeclareUnicodeCharacter{03A9}{\ensuremath{\Omega}}
    \DeclareUnicodeCharacter{03C5}{\ensuremath{\upsilon}}
    \DeclareUnicodeCharacter{03A5}{\ensuremath{\Upsilon}}
    \DeclareUnicodeCharacter{2113}{\ell}

    \DeclareUnicodeCharacter{221A}{\ensuremath{\sqrt{}}}
    \DeclareUnicodeCharacter{2264}{\leq}
    \DeclareUnicodeCharacter{2265}{\geq}
    \DeclareUnicodeCharacter{221E}{\infty}
    \DeclareUnicodeCharacter{2211}{\sum}
    \DeclareUnicodeCharacter{2208}{\in}
    \DeclareUnicodeCharacter{2209}{\notin}
    \DeclareUnicodeCharacter{2202}{\partial}
    \DeclareUnicodeCharacter{222B}{\ensuremath{\int}}
    \DeclareUnicodeCharacter{2148}{\id}
    \DeclareUnicodeCharacter{2248}{\approx}
    \DeclareUnicodeCharacter{2260}{\neq}
    \DeclareUnicodeCharacter{00B1}{\pm}
    \DeclareUnicodeCharacter{2A02}{\otimes}
    \DeclareUnicodeCharacter{2A01}{\oplus}
    \DeclareUnicodeCharacter{00BD}{\nicefrac{1}{2}}
    \DeclareUnicodeCharacter{00D7}{\times}
    \DeclareUnicodeCharacter{00B7}{\cdot}
    \DeclareUnicodeCharacter{230A}{\lfloor}
    \DeclareUnicodeCharacter{230B}{\rfloor}
    \DeclareUnicodeCharacter{2308}{\lceil}
    \DeclareUnicodeCharacter{2309}{\rceil}
    \DeclareUnicodeCharacter{22C5}{\ensuremath{\cdot}}

    \newcommand{\sageMexSymbol}[1]
    {{\fontencoding{OMX}\fontfamily{cmex}\selectfont\raisebox{0.75em}{\symbol{#1}}}}
    \DeclareUnicodeCharacter{239B}{\sageMexSymbol{"30}} % parenlefttp
    \DeclareUnicodeCharacter{239C}{\sageMexSymbol{"42}} % parenleftex
    \DeclareUnicodeCharacter{239D}{\sageMexSymbol{"40}} % parenleftbt
    \DeclareUnicodeCharacter{239E}{\sageMexSymbol{"31}} % parenrighttp
    \DeclareUnicodeCharacter{239F}{\sageMexSymbol{"43}} % parenrightex
    \DeclareUnicodeCharacter{23A0}{\sageMexSymbol{"41}} % parenrightbt
    \DeclareUnicodeCharacter{23A1}{\sageMexSymbol{"32}} % bracketlefttp
    \DeclareUnicodeCharacter{23A2}{\sageMexSymbol{"36}} % bracketleftex
    \DeclareUnicodeCharacter{23A3}{\sageMexSymbol{"34}} % bracketleftbt
    \DeclareUnicodeCharacter{23A4}{\sageMexSymbol{"33}} % bracketrighttp
    \DeclareUnicodeCharacter{23A5}{\sageMexSymbol{"37}} % bracketrightex
    \DeclareUnicodeCharacter{23A6}{\sageMexSymbol{"35}} % bracketrightbt

    \DeclareUnicodeCharacter{23A7}{\sageMexSymbol{"38}} % curly brace left top
    \DeclareUnicodeCharacter{23A8}{\sageMexSymbol{"3C}} % curly brace left middle
    \DeclareUnicodeCharacter{23A9}{\sageMexSymbol{"3A}} % curly brace left bottom
    \DeclareUnicodeCharacter{23AA}{\sageMexSymbol{"3E}} % curly brace extension
    \DeclareUnicodeCharacter{23AB}{\sageMexSymbol{"39}} % curly brace right top
    \DeclareUnicodeCharacter{23AC}{\sageMexSymbol{"3D}} % curly brace right middle
    \DeclareUnicodeCharacter{23AD}{\sageMexSymbol{"3B}} % curly brace right bottom
    \DeclareUnicodeCharacter{23B0}{\{} % 2-line curly brace left top half  (not in cmex)
    \DeclareUnicodeCharacter{23B1}{\}} % 2-line curly brace right top half (not in cmex)

    \DeclareUnicodeCharacter{2320}{\ensuremath{\int}} % top half integral
    \DeclareUnicodeCharacter{2321}{\ensuremath{\int}} % bottom half integral
    \DeclareUnicodeCharacter{23AE}{\ensuremath{\|}} % integral extenison

    \DeclareUnicodeCharacter{2571}{/}   % Box drawings light diagonal upper right to lower left
\fi

\let\textLaTeX\LaTeX
\renewcommand*{\LaTeX}{\hbox{\textLaTeX}}
"""

####################################################
# add LaTeX macros for Sage

from sage.misc.latex_macros import sage_latex_macros

try:
    pngmath_latex_preamble  # check whether this is already defined
except NameError:
    pngmath_latex_preamble = ""

for macro in sage_latex_macros():
    # used when building latex and pdf versions
    latex_elements['preamble'] += macro + '\n'
    # used when building html version
    pngmath_latex_preamble += macro + '\n'

# -- Options for manual page output ---------------------------------------

# One entry per manual page. List of tuples
# (source start file, name, description, authors, manual section).
man_pages = [
    (master_doc, 'mod-pgroupcohomology', u'"mod-p group cohomology" Documentation',
     [author], 1)
]


# -- Options for Texinfo output -------------------------------------------

# Grouping the document tree into Texinfo files. List of tuples
# (source start file, target name, title, author,
#  dir menu entry, description, category)
texinfo_documents = [
    (master_doc, 'mod-pgroupcohomology', u'"mod-p group cohomology" Documentation',
     author, 'mod-pgroupcohomology', 'One line description of project.',
     'Miscellaneous'),
]

###############
## Doc processing

#####################################################

def process_docstring_aliases(app, what, name, obj, options, docstringlines):
    """
    Change the docstrings for aliases to point to the original object.
    """
    basename = name.rpartition('.')[2]
    if hasattr(obj, '__name__') and obj.__name__ != basename:
        docstringlines[:] = ['See :obj:`%s`.' % name]

def process_directives(app, what, name, obj, options, docstringlines):
    """
    Remove 'nodetex' and other directives from the first line of any
    docstring where they appear.
    """
    if len(docstringlines) == 0:
        return
    first_line = docstringlines[0]
    directives = [ d.lower() for d in first_line.split(',') ]
    if 'nodetex' in directives:
        docstringlines.pop(0)

def process_docstring_cython(app, what, name, obj, options, docstringlines):
    """
    Remove Cython's filename, location and argspec embedding.
    """
    if len(docstringlines) <= 1:
        return
    if what == 'function':
        embedded_name = '.'.join(name.split('.')[-1:])
    else:
        embedded_name = '.'.join(name.split('.')[-2:])
    #~ print embedded_name, name,what
    while len(docstringlines) > 1:
        first_line = docstringlines[0].strip()
        # Filename/location
        if first_line.startswith('File:') and '(starting at' in first_line:
            #Remove the first two lines
            docstringlines.pop(0)
            docstringlines.pop(0)
        elif first_line.startswith(embedded_name):
            args = first_line.split(embedded_name,1)[1]
            if args.startswith('(') and args.endswith(')'):
                #Remove the first line
                docstringlines.pop(0)
            else:
                return
        else:
            return

def process_docstring_module_title(app, what, name, obj, options, docstringlines):
    """
    Removes the first line from the beginning of the module's docstring.  This
    corresponds to the title of the module's documentation page.
    """
    if what != "module":
        return

    #Remove any additional blank lines at the beginning
    title_removed = False
    while len(docstringlines) > 1 and not title_removed:
        if docstringlines[0].strip() != "":
            title_removed = True
        docstringlines.pop(0)

    #Remove any additional blank lines at the beginning
    while len(docstringlines) > 1:
        if docstringlines[0].strip() == "":
            docstringlines.pop(0)
        else:
            break

def process_dollars(app, what, name, obj, options, docstringlines):
    r"""
    Replace dollar signs with backticks.

    See sage.misc.sagedoc.process_dollars for more information.
    """
    if len(docstringlines) and name.find("process_dollars") == -1:
        from six.moves import range
        from sage.misc.sagedoc import process_dollars as sagedoc_dollars
        s = sagedoc_dollars("\n".join(docstringlines))
        lines = s.split("\n")
        for i in range(len(lines)):
            docstringlines[i] = lines[i]

def process_inherited(app, what, name, obj, options, docstringlines):
    """
    If we're including inherited members, omit their docstrings.
    """
    if not options.get('inherited-members'):
        return

    if what in ['class', 'data', 'exception', 'function', 'module']:
        return

    name = name.split('.')[-1]

    if what == 'method' and hasattr(obj, 'im_class'):
        if name in obj.im_class.__dict__.keys():
            return

    if what == 'attribute' and hasattr(obj, '__objclass__'):
        if name in obj.__objclass__.__dict__.keys():
            return

    for i in range(len(docstringlines)):
        docstringlines.pop()

##########################################
#
#  Connecting with app

from sage.misc.sageinspect import sage_getargspec
autodoc_builtin_argspec = sage_getargspec

def setup(app):
    app.connect('autodoc-process-docstring', process_docstring_cython)
    app.connect('autodoc-process-docstring', process_directives)
    app.connect('autodoc-process-docstring', process_docstring_module_title)
    app.connect('autodoc-process-docstring', process_dollars)
    app.connect('autodoc-process-docstring', process_inherited)
    #~ app.connect('autodoc-skip-member', skip_member)

    #~ # When building the standard docs, app.srcdir is set to COHO_DOC_SRC +
    #~ # 'LANGUAGE/DOCNAME', but when doing introspection, app.srcdir is
    #~ # set to a temporary directory.  We don't want to use intersphinx,
    #~ # etc., when doing introspection.
    #~ if app.srcdir.startswith(COHO_DOC_SRC):
        #~ app.add_config_value('intersphinx_mapping', {}, False)
        #~ app.add_config_value('intersphinx_cache_limit', 5, False)
        #~ # We do *not* fully initialize intersphinx since we call it by hand
        #~ # in find_sage_dangling_links.
        #~ #   app.connect('missing-reference', missing_reference)
        #~ app.connect('missing-reference', find_sage_dangling_links)
        #~ import sphinx.ext.intersphinx
        #~ app.connect('builder-inited', set_intersphinx_mappings)
        #~ app.connect('builder-inited', sphinx.ext.intersphinx.load_mappings)
        #~ app.connect('builder-inited', nitpick_patch_config)
