MAKE_OPTS:= --no-builtin-rules
CAMLPKGS ?= -package yojson

TEST_GOALS:=$(filter test%, $(MAKECMDGOALS))

.PHONY: submake
submake: Makefile.rocq
	$(MAKE) $(MAKE_OPTS) -f Makefile.rocq CAMLPKGS="$(CAMLPKGS)" $(filter-out test%, $(MAKECMDGOALS))
	+$(if $(TEST_GOALS),$(MAKE) $(MAKE_OPTS) -C tests $(patsubst tests/%,%,$(filter-out test, $(TEST_GOALS))))

# coq_makefile passes CAMLPKGS as compile/link flags but omits them from the
# generated plugin META, so `Declare ML Module` cannot dynlink yojson.  Patch
# the generated META to add yojson to its findlib requires.
Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f $< -o $@
	@sed 's/\(requires = "rocq-runtime.plugins.ltac\)"/\1 yojson"/' src/META.coq-lean-import > src/META.coq-lean-import.tmp
	@mv src/META.coq-lean-import.tmp src/META.coq-lean-import

%:: submake ;

# known sources

Makefile: ;

_CoqProject: ;
