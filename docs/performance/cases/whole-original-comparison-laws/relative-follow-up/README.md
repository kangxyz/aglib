# Relative inverse rectangle: retain the original equality transport

This follow-up extends the existing whole-original-comparison case. It concerns the ordinary `RelativeCohomologySquare` coefficient law and its lower `InverseRectangle` helper, not the whole étale migration. The accepted source/review handback and immutable source, run, diagnostic and review evidence are in [evidence](evidence/RELATIVE-PERFORMANCE-FINAL.json). The existing case and its earlier evidence remain intact.

## Failure and formation probe

Native source [1d32](evidence/sources/old-RelativeCohomologySquare.lean), SHA-256 `1d32a4d082077ae138d4a7f63a616ecdae398a2efcc35eb49d97d3ee09a03274`, failed in [remote-73e08631](evidence/runs/remote-73e08631689f43e2ab14fa0e1544ffee/receipt.json), SOURCE `f204986329b4dccb6264cff6af24f682a6f6db14ce2f90b8a397ec36e10bf75f`. Its [log](evidence/runs/remote-73e08631689f43e2ab14fa0e1544ffee/build.log) reports a kernel deterministic timeout at 36:8; the unknown prior constant at 90:8 is a cascade. The reported 279 seconds is the whole Relative module, within a 283-second pair phase, not an isolated kernel interval.

The [formation diagnostic](evidence/formation/RelativeFormation.lean) tested the exact proposition P36 as `(_h : P) : True` at the actual native module name, `isModule`, four library options, pins and 200000-heartbeat profile. [remote-f261f4e5](evidence/runs/remote-f261f4e505e3477fa29f78df2a07cd6b/receipt.json) closed with exit 0, one frontend and a 9.634-second phase. Its [log](evidence/runs/remote-f261f4e505e3477fa29f78df2a07cd6b/build.log) records the exact setup and command and a 3.007-second command wall time. This is proposition formation only: P was not proved and the native module was not closed by the probe.

## Whole isomorphisms and the actual indexed transport

First derive the whole triangle-square law on the five original native comparison isomorphisms, using their proved identities to the same `schemeAdjunctionData`, before choosing a coefficient `F`. Then perform inverse and prefix cancellation in a generic variable-category evaluator. Retain the actual inverse-image indexing functor family `K` and rectangle equality `hRect` through that evaluator, so its conclusion already contains the original objectwise `eqToHom` transport; instantiate the native coefficient only at the final application. This keeps the original values and the transport in the theorem actually consumed rather than substituting a same-endpoint comparison.

The selected sources retain all three original native headers, the later two bodies and imports, and all pre-existing lower declarations. They retain the same adjunction data, original five isomorphisms and proved identifications, six independent category/Hom worlds, and the same indexed family and literal transport. The accepted source record does not introduce a reference diagram, replacement cohomology model, desired-rectangle premise, new geometry, or changes to limits, pins, trust or options. The independent review's supported whole-five-Iso argument is recorded in the [review](evidence/review/whole-w10-final-continuation.md) and [JSON](evidence/review/whole-w10-final-continuation.json); it is separate from the compiler result.

## Source-bound native pass

The selected lower source [20269](evidence/sources/InverseRectangle.lean) has SHA-256 `20269ada008afa55594a013ffbb89663a89edeaf778f405ce948843895bfdd48`; the native source [e449](evidence/sources/RelativeCohomologySquare.lean) has SHA-256 `e44959c6c7941a1e64cb440000dd09a0838b11e3ccd013784f09ef981459dd9d`. Their [delta](evidence/DELTA.patch), [source handback](evidence/LIVE_READY.json) and [input manifest](evidence/inputs-manifest.json) preserve the actual source and dependency binding. The manifest SHA-256 is `01badda171a0807af24baef42d0423b9953347b87bcbb2dbc49fbd992d6dd5f8`.

[remote-db7da794](evidence/runs/remote-db7da79424ff40d3a7fae69729aa98ed/receipt.json), SOURCE `4e1ce6c796fe6bf4c901069b53bcca1fcabb806551daab9d09325106e9d72674`, closed exit 0 with two fresh frontend passes and a 34.96372678875923-second phase under the unchanged native profile. The [events](evidence/runs/remote-db7da79424ff40d3a7fae69729aa98ed/compiler-events.jsonl) and [log](evidence/runs/remote-db7da79424ff40d3a7fae69729aa98ed/build.log) retain actual coverage; Lake's 3473 jobs are not 3473 fresh frontends. The recorded command was:

```sh
/root/autodl-tmp/lean-build/elan/toolchains/leanprover--lean4---v4.34.1/bin/lake --rehash build Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativeCohomologySquare
```

This remote path identifies the original invocation, not a portable replay. The pass closes these source-bound ordinary modules, with the accepted source contract; downstream consumers and whole W10/étale closure remain separate. Changed inputs and run conditions do not establish a controlled speedup. Neither the failure nor the formation result identifies a unique expensive kernel pair or cause.

The small packet includes the complete three run receipts, logs and events, original and selected source bytes, formation source and result, accepted review, source manifest and delta. From `evidence/`, `shasum -a 256 -c SHA256SUMS` verifies the packet; no new compiler, review or audit run is implied.
