CC = cc
CFLAGS = -O2 -std=c11 -Wall -Wextra -Wpedantic
LDLIBS = -lm
# Cygwin's main thread has the stack its executable reserves, less than the
# 8 MB elsewhere: evaluation nests 5000 deep before TLC's StackOverflowError.
ifneq ($(findstring CYGWIN,$(shell uname)),)
LDLIBS += -Wl,--stack,67108864
endif
# AddressSanitizer hangs at startup on recent macOS; there, Guard Malloc
# catches overruns and use-after-free instead.
ifeq ($(shell uname),Darwin)
SANITIZERS = undefined
SANITIZE_ENV = DYLD_INSERT_LIBRARIES=/usr/lib/libgmalloc.dylib
# Guard Malloc gives each allocation pages of its own, never reused: the
# solver's many small ones run past the runners' memory limits.
SYM_ENV =
else
# Leaks are checked as manyan_check returns, not at an exit from an error;
# AddressSanitizer's larger frames need more than 8 MB of stack for 5000
# nested definitions.
SANITIZERS = address,undefined
SANITIZE_DEFS = -DMANYAN_LEAK_CHECK
SANITIZE_ENV = ulimit -s 65536 && ASAN_OPTIONS=leak_check_at_exit=0
SYM_ENV = $(SANITIZE_ENV)
endif
PREFIX ?= /usr/local
OBJDIR = .obj

# TLA+ tools 1.8.0, the oracle, pinned by checksum. 1.8.0 is a pre-release,
# whose jar can be rebuilt under the same tag: this one is commit bc1b506bdcad
# (its manifest's X-Git-Revision), built 2026-11-15.
TLA_JAR = $(OBJDIR)/tla/tla2tools.jar
TLA_URL = https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
TLA_SHA256 = 7e53aa636dac8a3cb0533f343115c0548e03fc0ce5edc7739becf58d3d0fb84f
# CommunityModules on TLC's class path, as tlaplus/Examples' CI puts it,
# give the modules of its names, such as IOUtils, their Java operators.
COMMUNITY_REV = 202611060952
COMMUNITY_SHA256 = a3b27c40f1fb5085f30c6ead37e918457f8cfc62c1e50a1dc668ef592ad2b5fb
COMMUNITY = $(OBJDIR)/CommunityModules-$(COMMUNITY_REV)
JAVA ?= $(firstword $(wildcard /opt/homebrew/opt/openjdk/bin/java) java)
TLC_CP = $(abspath $(TLA_JAR)):$(abspath $(COMMUNITY)/modules.jar)
TLC = $(JAVA) -XX:+UseParallelGC -cp $(TLC_CP) tlc2.TLC
SANY = $(JAVA) -XX:+UseParallelGC -cp $(TLC_CP) tla2sany.SANY
# Apalache 0.63.0, the oracle of -symbolic, pinned by checksum; it runs
# on the same Java.
APALACHE_VERSION = 0.63.0
APALACHE_URL = https://github.com/apalache-mc/apalache/releases/download/v$(APALACHE_VERSION)/apalache-$(APALACHE_VERSION).tgz
APALACHE_SHA256 = a756e96af249bf33cd7629667a49472cb26ac8227c48583da139b414834d59df
APALACHE = $(OBJDIR)/apalache-$(APALACHE_VERSION)/bin/apalache-mc
# TLAPS, the oracle of `fuzz.py prove`: the binaries of its rolling
# 1.6.0 pre-release, which have no checksum to pin (tlapm --version names
# the commit).
TLAPS_ARCH = $(if $(findstring Darwin,$(shell uname)),arm64-darwin,x86_64-linux-gnu)
TLAPS_URL = https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-$(TLAPS_ARCH).tar.gz
TLAPS = $(OBJDIR)/tlaps-1.6.0-pre/tlapm/bin/tlapm
APALACHE_RUN = env $(if $(findstring /,$(JAVA)),JAVA_HOME=$(abspath $(dir $(JAVA))..)) JVM_ARGS=-Xmx2g $(abspath $(APALACHE))

.PHONY: all lib test test-spec test-again test-spec-oracle bless test-symbolic test-symbolic-oracle bless-symbolic test-typecheck test-typecheck-oracle bless-typecheck test-lint test-lint-oracle bless-lint test-fmt test-fmt-oracle bless-fmt test-tla tla-tools wasm test-javascript site sanitize sanitize-linux fuzz fuzz-fmt fuzz-fmt-oracle fuzz-lint fuzz-lint-oracle fuzz-typecheck fuzz-sym fuzz-oracle fuzz-sim fuzz-check fuzz-live fuzz-prove fuzz-ref fuzz-model fuzz-model-simulate fuzz-model-symbolic bench full-bench full-bench-symbolic etcd-bench install clean

all: manyan

# ./manyan is profile-guided: the conformance suite is the training run.
# Without python3 to run it (or, with clang, llvm-profdata to merge the
# profile), ./manyan is a plain build.
PGO = $(abspath $(OBJDIR))/pgo
PYTHON = $(shell command -v python3)
ifneq ($(findstring clang,$(shell $(CC) --version 2>/dev/null)),)
PROFDATA ?= $(shell xcrun -f llvm-profdata 2>/dev/null || command -v llvm-profdata)
PGO_TOOLS = $(and $(PYTHON),$(PROFDATA))
PGO_GEN = -fprofile-instr-generate
PGO_USE = -fprofile-instr-use=$(PGO)/manyan.profdata
PGO_MERGE = $(PROFDATA) merge -o $(PGO)/manyan.profdata $(PGO)/*.profraw
else
PGO_TOOLS = $(PYTHON)
PGO_GEN = -fprofile-generate=$(PGO)
PGO_USE = -fprofile-use=$(PGO) -fprofile-partial-training
PGO_MERGE = true
endif

SRC = manyan.c manyan-std.c
HDR = manyan.h manyan-std.h

manyan: $(SRC) $(HDR)
ifeq ($(PGO_TOOLS),)
	$(CC) $(CFLAGS) $(LDFLAGS) $(SRC) $(LDLIBS) -o $@
else
	rm -rf $(PGO) && mkdir -p $(PGO)
	$(CC) $(CFLAGS) $(PGO_GEN) $(LDFLAGS) $(SRC) $(LDLIBS) -o $(PGO)/manyan
	LLVM_PROFILE_FILE=$(PGO)/%p.profraw $(PYTHON) tests/spec_runner.py $(PGO)/manyan > /dev/null
	$(PGO_MERGE)
	$(CC) $(CFLAGS) $(PGO_USE) $(LDFLAGS) $(SRC) $(LDLIBS) -o $@
endif

test: test-spec test-result test-again test-python test-symbolic test-typecheck test-lint test-fmt

test-spec: manyan
	python3 tests/spec_runner.py ./manyan --strict
	python3 tests/spec_runner.py "./manyan -workers 4" --strict

# What a check found (ManyanOptions.result) is what it printed.
$(OBJDIR)/manyan-result: tests/result.c $(SRC) $(HDR)
	mkdir -p $(OBJDIR)
	$(CC) $(CFLAGS) $(LDFLAGS) tests/result.c manyan-std.c $(LDLIBS) -o $@

test-result: $(OBJDIR)/manyan-result
	python3 tests/spec_runner.py $(OBJDIR)/manyan-result --strict
	python3 tests/spec_runner.py "$(OBJDIR)/manyan-result -workers 4 -result result.json" --strict

# A second check in one process prints what a first does, every global reset.
$(OBJDIR)/manyan-again: tests/again.c $(SRC) $(HDR)
	mkdir -p $(OBJDIR)
	$(CC) $(CFLAGS) $(LDFLAGS) tests/again.c manyan-std.c $(LDLIBS) -o $@

test-again: $(OBJDIR)/manyan-again
	python3 tests/spec_runner.py $(OBJDIR)/manyan-again --strict
	python3 tests/spec_runner.py "$(OBJDIR)/manyan-again -workers 4" --strict
	python3 tests/symbolic_runner.py $(OBJDIR)/manyan-again --strict
	python3 tests/typecheck_runner.py $(OBJDIR)/manyan-again --strict
	python3 tests/lint_runner.py $(OBJDIR)/manyan-again --strict
	python3 tests/fmt_runner.py $(OBJDIR)/manyan-again --strict

# manyan.c and manyan-std.c built to link at run time, as the Python
# package's check() loads them.
SOEXT = $(if $(findstring Darwin,$(shell uname)),dylib,so)
LIB = libmanyan.$(SOEXT)
lib: $(LIB)
$(LIB): $(SRC) $(HDR)
	$(CC) $(CFLAGS) -shared -fPIC -DMANYAN_NO_MAIN $(LDFLAGS) $(SRC) $(LDLIBS) -o $@

# The Python package's run(), on this executable, and its check(), on this library.
test-python: manyan $(LIB)
	MANYAN_LIB=$(abspath $(LIB)) python3 python/test_manyan.py

# The oracle must agree with every expected output, which validates the tests.
test-spec-oracle: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/spec_runner.py ./manyan --strict --oracle "$(TLC)"

# Rewrite the expected outputs from the oracle (after adding a test).
bless: $(TLA_JAR) $(COMMUNITY)
	python3 tests/spec_runner.py ./manyan --oracle "$(TLC)" --bless $(if $(ONLY),--only $(ONLY))

# -symbolic against Apalache: the outcome of each test in tests/symbolic.
test-symbolic: manyan
	python3 tests/symbolic_runner.py ./manyan --strict

test-symbolic-oracle: manyan $(APALACHE)
	python3 tests/symbolic_runner.py ./manyan --strict --oracle "$(APALACHE_RUN)"

bless-symbolic: $(APALACHE)
	python3 tests/symbolic_runner.py ./manyan --oracle "$(APALACHE_RUN)" --bless $(if $(ONLY),--only $(ONLY))

# -typecheck against Apalache: the outcome of each test in tests/typecheck.
test-typecheck: manyan
	python3 tests/typecheck_runner.py ./manyan --strict

test-typecheck-oracle: manyan $(APALACHE)
	python3 tests/typecheck_runner.py ./manyan --strict --oracle "$(APALACHE_RUN)"

bless-typecheck: $(APALACHE)
	python3 tests/typecheck_runner.py ./manyan --oracle "$(APALACHE_RUN)" --bless $(if $(ONLY),--only $(ONLY))

# -lint against SANY: syntax, semantics, levels and warnings in tests/lint.
test-lint: manyan
	python3 tests/lint_runner.py ./manyan --strict

test-lint-oracle: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/lint_runner.py ./manyan --strict --oracle "$(SANY)"

bless-lint: $(TLA_JAR) $(COMMUNITY)
	python3 tests/lint_runner.py ./manyan --oracle "$(SANY)" --bless $(if $(ONLY),--only $(ONLY))

# -fmt: canonical layout, idempotence, and SANY validity in tests/fmt.
test-fmt: manyan
	python3 tests/fmt_runner.py ./manyan --strict

test-fmt-oracle: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/fmt_runner.py ./manyan --strict --oracle "$(SANY)"

bless-fmt: manyan
	python3 tests/fmt_runner.py ./manyan --bless $(if $(ONLY),--only $(ONLY))

$(TLAPS):
	rm -rf $(OBJDIR)/tlaps-1.6.0-pre && mkdir -p $(OBJDIR)/tlaps-1.6.0-pre
	curl -fsSL $(TLAPS_URL) | tar xz -C $(OBJDIR)/tlaps-1.6.0-pre
	touch $@

$(APALACHE):
	mkdir -p $(OBJDIR)
	curl -fsSL -o $(OBJDIR)/apalache.tgz.tmp $(APALACHE_URL)
	echo "$(APALACHE_SHA256)  $(OBJDIR)/apalache.tgz.tmp" | shasum -a 256 -c -
	tar xzf $(OBJDIR)/apalache.tgz.tmp -C $(OBJDIR) && rm $(OBJDIR)/apalache.tgz.tmp
	touch $@

test-tla: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/tla_check.py ./manyan --tlc "$(TLC)"

tla-tools: $(TLA_JAR) $(COMMUNITY)
$(TLA_JAR):
	mkdir -p $(dir $@)
	curl -fsSL -o $@.tmp $(TLA_URL)
	echo "$(TLA_SHA256)  $@.tmp" | shasum -a 256 -c -
	mv $@.tmp $@

$(OBJDIR)/manyan-sanitize: $(SRC) $(HDR)
	mkdir -p $(OBJDIR)
	$(CC) $(CFLAGS) -O1 -g -fsanitize=$(SANITIZERS) -fno-sanitize-recover=all $(SANITIZE_DEFS) $(SRC) $(LDLIBS) -o $@

sanitize: $(OBJDIR)/manyan-sanitize
	$(SANITIZE_ENV) python3 tests/spec_runner.py $(OBJDIR)/manyan-sanitize --strict
	$(SYM_ENV) python3 tests/symbolic_runner.py $(OBJDIR)/manyan-sanitize --strict
	$(SANITIZE_ENV) python3 tests/typecheck_runner.py $(OBJDIR)/manyan-sanitize --strict
	$(SANITIZE_ENV) python3 tests/lint_runner.py $(OBJDIR)/manyan-sanitize --strict
	$(SANITIZE_ENV) python3 tests/fmt_runner.py $(OBJDIR)/manyan-sanitize --strict

# Mutated models must not crash the sanitized build; random expressions
# must print as TLC prints them; so must random simulations of the models.
# RUNS and SEED choose how many and which.
RUNS ?= 1000
SEED ?= 1
fuzz: $(OBJDIR)/manyan-sanitize
	$(SANITIZE_ENV) python3 tests/fuzz.py crash $(OBJDIR)/manyan-sanitize --runs $(RUNS) --seed $(SEED)

fuzz-fmt: $(OBJDIR)/manyan-sanitize
	$(SANITIZE_ENV) python3 tests/fuzz.py fmt $(OBJDIR)/manyan-sanitize --runs $(RUNS) --seed $(SEED)

fuzz-fmt-oracle: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/fuzz.py fmt ./manyan --sany "$(SANY)" --runs $(RUNS) --seed $(SEED)

fuzz-lint: $(OBJDIR)/manyan-sanitize
	$(SANITIZE_ENV) python3 tests/fuzz.py lint $(OBJDIR)/manyan-sanitize --runs $(RUNS) --seed $(SEED)

fuzz-lint-oracle: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/fuzz.py lint ./manyan --sany "$(SANY)" --runs $(RUNS) --seed $(SEED)

fuzz-typecheck: $(OBJDIR)/manyan-sanitize
	$(SANITIZE_ENV) python3 tests/fuzz.py typecheck $(OBJDIR)/manyan-sanitize --runs $(RUNS) --seed $(SEED)

fuzz-sym: $(OBJDIR)/manyan-sanitize
	$(SYM_ENV) python3 tests/fuzz.py sym $(OBJDIR)/manyan-sanitize --runs $(RUNS) --seed $(SEED)

# The same in Debian, with Docker, for a machine whose sanitizers find no
# leaks, as macOS's; its build apart from this one's.
sanitize-linux:
	docker run --rm -v "$(CURDIR)":/src -w /src debian:bookworm-slim sh -c \
	  'apt-get update -qq && apt-get install -y -qq gcc make python3 >/dev/null && \
	   make sanitize fuzz OBJDIR=.obj/linux RUNS=$(RUNS) SEED=$(SEED)'

fuzz-prove: manyan $(TLAPS)
	python3 tests/fuzz.py prove ./manyan --tlapm $(TLAPS) --runs $(RUNS) --seed $(SEED)

# The reference, and the proofs about it.
REF = lean/.lake/build/bin/ref
$(REF): lean/Main.lean lean/Ref/*.lean lean/lakefile.toml
	cd lean && lake build && lake build Ref.Sound Ref.Choice

fuzz-ref: manyan $(REF)
	python3 tests/fuzz.py ref ./manyan --ref $(REF) --runs $(RUNS) --seed $(SEED)

fuzz-model: manyan $(REF)
	python3 tests/fuzz.py model ./manyan --ref $(REF) --runs $(RUNS) --seed $(SEED)

fuzz-model-simulate: manyan $(REF)
	python3 tests/fuzz.py model ./manyan --ref $(REF) --simulate --runs $(RUNS) --seed $(SEED)

fuzz-model-symbolic: manyan $(REF)
	python3 tests/fuzz.py model ./manyan --ref $(REF) --symbolic --runs $(RUNS) --seed $(SEED)

fuzz-oracle: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/fuzz.py diff ./manyan --tlc "$(TLC)" --runs $(RUNS) --seed $(SEED)

fuzz-sim: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/fuzz.py sim ./manyan --tlc "$(TLC)" --runs $(RUNS) --seed $(SEED)

fuzz-check: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/fuzz.py check ./manyan --tlc "$(TLC)" --runs $(RUNS) --seed $(SEED)

fuzz-live: manyan $(TLA_JAR) $(COMMUNITY)
	python3 tests/fuzz.py live ./manyan --tlc "$(TLC)" --runs $(RUNS) --seed $(SEED)

bench: manyan $(TLA_JAR) $(COMMUNITY)
	python3 bench/compare.py ./manyan --tlc "$(TLC)"

# tlaplus/Examples, pinned, with the TLAPS modules its CI puts on TLC's
# class path too. Move a pin with its date in the commit.
EXAMPLES_REV = ca168055339d5cbcee95b7eefcb97c1ee59f9914
TLAPM_REV = c8ddc44a80b621989f96a9ee2c371301c52b109f
EXAMPLES = $(OBJDIR)/Examples-$(EXAMPLES_REV)
TLAPM = $(OBJDIR)/tlapm-$(TLAPM_REV)
FULL_TLC = $(JAVA) -XX:+UseParallelGC -cp $(TLC_CP):$(abspath $(TLAPM)/library) tlc2.TLC

# ONLY=PATTERN picks models; MAX_RUNTIME=hh:mm:ss caps the manifest's runtime,
# or all takes every model; TIMEOUT=S kills a run past S seconds (900).
full-bench: manyan $(TLA_JAR) $(COMMUNITY) $(EXAMPLES) $(TLAPM)
	python3 bench/examples.py ./manyan --tlc "$(FULL_TLC)" --examples $(EXAMPLES) \
		--library $(COMMUNITY) --library $(TLAPM)/library \
		$(if $(ONLY),--only $(ONLY)) $(if $(MAX_RUNTIME),--max-runtime $(MAX_RUNTIME)) $(if $(TIMEOUT),--timeout $(TIMEOUT))

# The models tlaplus/Examples checks with Apalache, with -symbolic.
full-bench-symbolic: manyan $(APALACHE) $(COMMUNITY) $(EXAMPLES) $(TLAPM)
	python3 bench/symbolic.py ./manyan --apalache "$(APALACHE_RUN)" --examples $(EXAMPLES) \
		--library $(COMMUNITY) --library $(TLAPM)/library $(if $(ONLY),--only $(ONLY))

# etcd-io/raft, pinned: its trace validation, with the traces its
# interaction tests log (needs Go). ONLY=PATTERN picks traces.
RAFT_REV = 99f9ffb3d19c2dee73cc802737cd7e1e5f008986
RAFT = $(OBJDIR)/raft-$(RAFT_REV)

etcd-bench: manyan $(TLA_JAR) $(COMMUNITY) $(RAFT)
	python3 bench/etcd.py ./manyan --tlc "$(TLC)" --raft $(RAFT) \
		--library $(COMMUNITY) $(if $(ONLY),--only $(ONLY))

$(OBJDIR)/raft-%:
	rm -rf $@.tmp && git init -q $@.tmp
	git -C $@.tmp fetch -q --depth 1 https://github.com/etcd-io/raft $*
	git -C $@.tmp checkout -q FETCH_HEAD && mv $@.tmp $@

$(OBJDIR)/Examples-%:
	rm -rf $@.tmp && git init -q $@.tmp
	git -C $@.tmp fetch -q --depth 1 https://github.com/tlaplus/Examples $*
	git -C $@.tmp checkout -q FETCH_HEAD && mv $@.tmp $@

$(OBJDIR)/tlapm-%:
	rm -rf $@.tmp && git init -q $@.tmp
	git -C $@.tmp fetch -q --depth 1 https://github.com/tlaplus/tlapm $*
	git -C $@.tmp checkout -q FETCH_HEAD && mv $@.tmp $@

$(COMMUNITY):
	rm -rf $@.tmp && mkdir -p $@.tmp
	curl -fsSL -o $@.tmp/modules.jar https://github.com/tlaplus/CommunityModules/releases/download/$(COMMUNITY_REV)/CommunityModules-deps.jar
	echo "$(COMMUNITY_SHA256)  $@.tmp/modules.jar" | shasum -a 256 -c -
	cd $@.tmp && unzip -q modules.jar '*.tla'
	mv $@.tmp $@

# The npm package (javascript/): manyan compiled to WebAssembly with
# Emscripten, its files in memory; the conformance suite runs it through
# javascript/cli.js. Evaluation nests as deep as natively, on a stack as
# large as Cygwin's. Binaryen inlines no function into another: the
# evaluator's frames stay small, so a browser's stack holds more of them.
EMCC ?= emcc
WASM_FLAGS = -O3 -std=c11 -sSUPPORT_LONGJMP=wasm -fwasm-exceptions \
	-sBINARYEN_EXTRA_PASSES=--one-caller-inline-max-function-size=0,--flexible-inline-max-function-size=0
WASM_LDFLAGS = -sMODULARIZE -sEXPORT_ES6 -sENVIRONMENT=web,worker,node -sINVOKE_RUN=0 -sEXIT_RUNTIME \
	-sALLOW_MEMORY_GROWTH -sMAXIMUM_MEMORY=4GB -sSTACK_SIZE=64MB -sINITIAL_MEMORY=128MB -sFORCE_FILESYSTEM \
	-sEXPORTED_RUNTIME_METHODS=callMain,FS

wasm: javascript/manyan.mjs
javascript/manyan.mjs: $(SRC) $(HDR)
	$(EMCC) $(WASM_FLAGS) $(WASM_LDFLAGS) $(SRC) -o $@
	cp LICENSE javascript/LICENSE

test-javascript: javascript/manyan.mjs
	python3 tests/spec_runner.py "node $(abspath javascript/cli.js)" --strict --no-exec
	cd javascript && node test.mjs

# The site gh-pages serves: docs/ as HTML pages (docs/site.py, which needs
# Python-Markdown), the playground's WebAssembly beside them, and DieHard
# for it to start from.
site: javascript/manyan.mjs
	rm -rf $(OBJDIR)/site && mkdir -p $(OBJDIR)/site/manyan
	python3 docs/site.py $(OBJDIR)/site
	cp docs/logo.jpg examples/DieHard.tla examples/DieHard.cfg $(OBJDIR)/site/
	cp javascript/index.js javascript/engine.js javascript/worker.js javascript/manyan.mjs javascript/manyan.wasm $(OBJDIR)/site/manyan/
	git rev-parse HEAD > $(OBJDIR)/site/commit.txt
	touch $(OBJDIR)/site/.nojekyll

install: manyan
	install -d $(DESTDIR)$(PREFIX)/bin $(DESTDIR)$(PREFIX)/include
	install manyan $(DESTDIR)$(PREFIX)/bin/manyan
	install -m 644 manyan.h manyan-std.h $(DESTDIR)$(PREFIX)/include/

clean:
	rm -f manyan libmanyan.so libmanyan.dylib javascript/manyan.mjs javascript/manyan.wasm
