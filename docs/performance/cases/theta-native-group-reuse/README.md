# Reuse the selected native group before forming theta equations

The complete geometric-positive theorem uses the original scalar-extended
Jacobian `A = J_K`, the original Jacobian `B = Jac(X_K)`, its actual source
comparison, and the supplied Picard representatives. The successful repair
binds the already selected canonical group of `B` before constructing `e`,
`hInv`, `hpull` and `H`:

```lean
let B := picardIdentityComponent X'.hom P' R'
let : GrpObj B := grpObjPicardIdentityComponent X'.hom P' R'
```

This is construction-time reuse of the same native instance. The canonical
instance is defined using the same `picardCommGrpObj` and
`grpObjIdentityComponentOver`; see the preserved
[original supplier](sources/IdentityComponent.lean.txt). The change adds no
model, group law, representation or public premise. The statement-given
`scalarGroup` on `A`, the original coherent-H¹ premise, all geometric
hypotheses, maps and signs are unchanged.

## Actual failure, diagnostic and repair

The complete [failed producer](sources/FieldComparison.before.lean.txt),
SHA256 `1a08bab3062625be54b9dc6e0d4524a7bc6a6f7236e62748de238060c0778079`,
formed the original pullback calculation, but its application `H hpull hg'`
failed at the `hpull` argument with the default recursion limit. Its
[native receipt](evidence/failed/receipt.json), [complete log](evidence/failed/build.log)
and [compiler events](evidence/failed/compiler-events.jsonl) record
`remote-5dd38397193a4c4ab3a54c3ed31ae38d`, SOURCE
`90078dd5d9cda56049350ce8c0522bd21130befae4d30e3adf3a9b2637ac7ffa`,
exit 1, closed group and one failed Field frontend. The mirror was blocked.
Late normalization of the component, group wrapper and base aliases did
not close the application. The earlier
[late-normalization receipt](evidence/late-normalization/receipt.json) and
[log](evidence/late-normalization/build.log) preserve its actual e169 input.

The bounded diagnostic belongs to that earlier e169 input, not to the
successful producer. Its [full input](sources/FieldComparison.e169.lean.txt),
[actual diagnostic prefix](sources/FieldApplicationTypePrefix.lean.txt),
[inspector](sources/application-inspector.lean.txt),
[small validation source](sources/FieldApplicationToolValidation.lean.txt),
[receipt](evidence/diagnostic/receipt.json),
[full log](evidence/diagnostic/build.log),
[29 actual records and setup/source identities](evidence/diagnostic/actual-records.json)
and [complete bounded report](evidence/diagnostic/actual-report.txt) retain
its scope. The equation carrier and genus premise were raw-identical;
the observed inversion-instance heads differed as
`grpObjPicardIdentityComponent` and `grpObjIdentityComponentOver`.
Default premise conversion still exceeded recursion. These first differences
do not identify a unique internal conversion or kernel cause.

The [one-line patch](repair.patch.json) moves instance reuse before equation
construction. It transforms the failed producer into the complete
[passed producer](sources/FieldComparison.passed.lean.txt), SHA256
`dc7bede6cfbafd989ca6181b7c05b21c4201017a86856bf9537a82b0fa0e1096`;
the [mirror](sources/FieldComparison.mirror.lean.txt), SHA256
`38bc0a4cadfb40c69fad6a09c5a8b0565438fe2a5b0c30ed0dfea2b7dd699387`,
is unchanged. All other failed-input source and normalization remain intact.
The [successful receipt](evidence/passed/receipt.json),
[complete log](evidence/passed/build.log) and
[events](evidence/passed/compiler-events.jsonl) record
`remote-0f87d2cb5ba24f9989c8b904f516eba2`, SOURCE
`3114ba4083e0dc539bf5009de9c42c939ee0d36b4175ede572fb7004bf4d904a`,
exit 0, closed group, two fresh successful producer/mirror frontends and no
diagnostics. The runs retain jobs 8, threads 4, Lean memory 12800 MiB,
RSS limit 110592 MiB and default proof/recursion limits, without cache cleaning
or workspace replacement.

## Source correspondence and limits

The [original source-manifest projection](evidence/source-manifest-projection.json)
retains SOURCE3114 metadata, original manifest hash, the exact eight family
hashes, pins and canonical supplier identity. It is explicitly a projection,
not a second full manifest. The
[author family identities](evidence/CONDITIONAL_PASS_IDENTITIES.json) and
[case metadata](case.json) retain original file provenance.
Lean is 4.34.1 and Mathlib is
`d13f23b723b8a846827a245b89c10fc7d3f11612`; the exact
[toolchain](sources/lean-toolchain.txt), [Lake configuration](sources/lakefile.toml.txt)
and [dependency manifest](sources/lake-manifest.json.txt) are preserved.
The source lane HEAD is `4447b30aa15a87a61987cc427aa36d1343e7c57e`.

The supported observation is ordinary default-budget closure of the complete
conditional Field producer and matching mirror. It includes scalar comparison,
fpqc isomorphism descent, the all-genus negative-inverse principal group/scheme
isomorphism and positive-genus ample-line-bundle morphism after algebraically
closed extension. The original coherent-H¹ inequality remains a premise;
this case proves no unconditional H¹ bound, ground-field theta bundle or
independent mathematical review. Its successful author snapshot differs from
the later ready union. Final native lint/style/axiom coverage belongs to its
own invocation and is not inferred here.

The 96.443-second failed run and 109.294-second successful producer/mirror run
are different outcomes on different whole source snapshots. They give no
matched timing speedup or unique-cause verdict. No compilation or benchmark
was added to preserve this documentation.

For ordinary reproduction, select the preserved producer and mirror against
the original compatible suppliers/pins through the existing guarded source
route, then build their in-package mirror incrementally:

```sh
lake build AglibTest.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.FieldComparison
```

Reuse compatible outputs; this historical recipe does not authorize replacing
live source or rebuilding unaffected modules. `SHA256SUMS` binds the preserved
case files. The patch is lossless UTF-8 JSON, with its original SHA256 and text;
decode its `text` field to recover the exact original patch bytes.
