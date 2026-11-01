# Original étale migration closeout

The accepted 27-source migration moves existing complete constructions and proofs to lower site, representable and torsor owners. Native sites use the same constructors and named original-value equations; maps, hypotheses and universe worlds are preserved. This applies the existing complete-construction and original-value method. It does not establish a new compiler cause or a controlled speedup.

[Source hashes](source-sha256.txt) identify the 27 files and base commit. The [patch](original27.patch) includes all 27 changes, including the 11 new source texts. Apply it to that base with `git apply original27.patch` from the checkout root. The source basis of the recorded remote run is `9918491d10c40660a40ea3c48817e2d9647f6f6609a57baa352a960ce8ff6e7d`.

The native incremental Lean build recorded 23 fresh compiler invocations, all passing, with zero failures; 23 counts invocations, not the 27 source files. Compatible cached coverage is retained rather than counted as fresh compilation. The [receipt](receipt.json) contains the exact command, input hashes, toolchain pins, environment and cache provenance; [compiler events](compiler-events.jsonl) and [raw log](build.log) supply the observed timings and output. Exit status was zero. These observations do not establish a whole hosted-CI pass. Other final necessary checks were pending at this record's preparation.


## Repaired declaration metadata and final current input

The initial 27-source patch, hashes and `9cfc` compiler evidence above remain
on their actual successful `991849` input. A single full stock declaration
environment then found two redundant or non-normal simp enrollments and two
unused target assumptions on one reusable Hom equivalence. The
[exact two-file repair](declaration-repair.patch) retains the equations, maps,
proof bodies and independent universes; main finite comparison endpoints keep
their hypotheses. The inverse-value formula retains the target assumptions
that its original preimage construction needs.

[Current source hashes](current-source-sha256.txt) and the
[current CPP receipt](current-cpp-receipt.json), [log](current-cpp-build.log)
and [events](current-cpp-compiler-events.jsonl) bind the affected successful
retry to its actual later input. Seven fresh frontends passed, with compatible
current ActionDescent and unchanged outputs retained from their producing
runs. These counts are not a forced fresh build of all 27 files.

The [final stock declaration log](current-declaration.log) and
[closed receipt](current-declaration-receipt.json) report success on that
current input. The native predicate and all linters are unchanged. The same
already-compiled import-only batch header is used as a checker environment,
with read-only links to the protected Linux artifacts; it contains no
declarations or API tests. Initial builtin, source style and approved-axiom
checks passed and are retained on their actual inputs.
[The final evidence map](final-checks.json) separates those scopes. No new
imports, proof bodies or foundations were introduced by the declaration
repair. Failed declaration and first repair feedback remain alongside the
passes. There was no kernel replay, external client check, larger budget,
linter suppression or new mathematical result. Hosted CI is a separate run.
