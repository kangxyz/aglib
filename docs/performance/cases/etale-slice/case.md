# Intrinsic slice presentation: shared native equation and typed product bridge

> Fixed performance case based on three recorded remote runs. Their actual source identities and diagnostic boundaries are retained; timings are not a matched benchmark.

## Reproduction identity

The native target checkout was at HEAD `54d6974ace11bf7d197aa925cb8cade86db8a24f`, with coordinated uncommitted changes, Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib pin `d13f23b723b8a846827a245b89c10fc7d3f11612`, and unchanged profile jobs 8, 4 threads per frontend, 12,800 MiB per frontend, 110,592 MiB aggregate, no CPU oversubscription. The recorded command uses `lake --rehash build`. The complete source manifests remain at their original R locators; bounded selected-source capsules list every Aglib import hash reached from these two roots. The passing current source is linked at [`Aglib/CategoryTheory/Topos/SlicePresentation.lean`](../../../../Aglib/CategoryTheory/Topos/SlicePresentation.lean); the actual consumer is [`Aglib/CategoryTheory/Topos/Slice/Grothendieck.lean`](../../../../Aglib/CategoryTheory/Topos/Slice/Grothendieck.lean). Their successful-run SHA-256 values are `7c9d08a3b001b8cc9eab19cd5af522883be3001d7715d0643b99abd82e39e0f2` and `2dfd8f69750b9749c23b61c58ea8031b687b772a5da5ed25828b5f1adc734187`.

Source traversal uses the native comment-aware `lean_tools.source.lean_imports` reader (nested comments and strings are masked before header parsing); each selected Aglib source hash matches its run’s full manifest. The capsule scope follows only Aglib imports reachable from `SlicePresentation` and the actual `Slice.Grothendieck` consumer. Mathlib and Lean inputs are represented by their pinned revisions/toolchain identity, not per-file upstream hashes. This coverage does not reproduce the other modules requested in the larger v4/v5 commands.

The v4 failing source is preserved verbatim as [`slice-presentation-v4-native-correspondence.lean.txt`](slice-presentation-v4-native-correspondence.lean.txt) (SHA-256 `aeb8c409ce35804dd7a0b8ea4cbc2c1aed4db809519955ac7e7cdf0864a73097`). The corresponding prior `Mates.Whole` snapshot is [`mates-whole-v4.lean.txt`](mates-whole-v4.lean.txt); its v4 run input hash is `1062ecc3bc4c3f4a816b33c87ea63633509a69af7a466aa2914f527d438f32a5`.

## Observed repair boundary

The failed v4 source reduced the concrete `restrictionStarIso_map_counit` equation at the selected concrete equivalence. In run `remote-01041402ec244c8fa67ea45af0c0bf04`, that theorem hit a kernel deterministic timeout at source line 651. The same frontend reported ordinary normalization, product/reflexivity, and elaboration errors. The `SlicePresentation` frontend failed after 153 s; the full remote command ended with exit 1 after 155.8 s. This records where the timeout was observed, not an isolated causal explanation. See the retained [v4 diagnostics](remote-01041402ec244c8fa67ea45af0c0bf04-diagnostics.log.txt) and [receipt](remote-01041402ec244c8fa67ea45af0c0bf04-receipt.json).

The shared-equation repair keeps the actual native construction `Iso.compInverseIso (H := e) alpha.symm` as `Construction.compInverseComparison` and proves `Construction.CompInverseCounitEq` over variable categories using the original counit naturality. The concrete `restrictionStarIso` and its counit comparison specialize those same proved heads. The intermediate v5 source (`3271faca603e39020f2262f4020ae8890a69e361d7b61ff1338bca80c0fe9516`) shares this construction/equation boundary; its run had five source errors, while the 12 pure mate owners and `EtaleCohomology.BaseChangeMap` passed. See its [diagnostics](remote-0825a8ce10854e49a7488fb686431c0b-diagnostics.log.txt) and [receipt](remote-0825a8ce10854e49a7488fb686431c0b-receipt.json).

The v6 source also states exact whole native equalities for the original `Over.star` maps. Its actual fibre is compared with the existing chosen product fibre through an explicit equivalence that is identity on original section values. This avoids rewriting across implicit `getLimitCone` carriers that print alike; `productFibreEquiv` and the original second-projection formula remain in use. The source preserves the original categories, maps, units/counits, paired `p,s(X,p)` section values and worlds. No product or sheaf model is reselected.

Run `remote-8c5ba5cbd63b45149e8a52cd3016b7e4` passed both the 929-line `SlicePresentation` frontend (14 s) and its actual `Slice.Grothendieck` consumer (2.1 s): two frontends, zero failed, no input drift, no OOM event, no forced kill, with the profile unchanged. The [recorded successful compiler output](remote-8c5ba5cbd63b45149e8a52cd3016b7e4-diagnostics.log.txt) and [receipt](remote-8c5ba5cbd63b45149e8a52cd3016b7e4-receipt.json) are retained.

## Interpretation and boundary

These runs support a narrow reusable method: share the actual native comparison constructor and prove its complete counit equation before specializing it; at native product boundaries, use typed whole equalities and an explicit identity-on-values bridge rather than relying on definitional equality of implicit limit-cone carriers. The concrete v6 case compiles; this record does not establish a universal compiler-cause claim or a new mathematical theorem.

The 153 s failed frontend and 14 s passing frontend are not a matched speedup: source changes are coupled and target sets differ. The receipt peak RSS is whole-group evidence, not per-file profiling. No higher theory, larger resource budget, global speedup or isolated cause is claimed. Earlier abstract-topos comparisons and conditional premises remain subject to existing review; this case does not grant established status. Root's final scoped checks and broader Étale dependent-consumer coverage remain open. The general sheafified-representable `h_U^#` presentation is outside this case.

The preserved v4 sources and the fixed [v4-to-v5 slice delta](slice-v4-to-v5.patch),
[v5-to-v6 slice delta](slice-v5-to-v6.patch), and
[old-to-current mate-owner delta](mates-whole-v4-to-v5.patch) recover the
intermediate source inputs without copying the current production files.
Their exact before/after and patch hashes are recorded in `case.json`.
