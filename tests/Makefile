MAKE_OPTS:= --no-builtin-rules

# init/stdlib NDJSON dumps are committed compressed (git-LFS); decompress them
# (once, if missing) before building the tests that import them.
DUMPS := ../dumps

.PHONY: submake
submake: Makefile.rocq
	@for f in init stdlib; do \
	  test -f $(DUMPS)/$$f.ndjson || \
	    ( cd $(DUMPS) && python3 -c "import zipfile; zipfile.ZipFile('$$f.ndjson.zip').extractall('.')" ); \
	done
	$(MAKE) $(MAKE_OPTS) -f Makefile.rocq $(MAKECMDGOALS)

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f $< -o $@

%:: submake ;

# known sources

Makefile: ;

_CoqProject: ;
