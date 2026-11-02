# Correspondence correction and bounded normalization continuation

The fixed COMPLETE3 **v2** mathematical verdict below is retained on its original `097432f2…/fb0b4a66…/89e372f5…` basis. It is not relabeled as the later current packet. Two bounded follow-ups are recorded here.

**Public helper signature claim withdrawn on v1–v3.** The old `CategoryTheory.Limits.constantDiagramColimitIso` header explicitly ordered `{I}{C}[Category I][Category C]`; the v1–v3 section variables produced `{I}[Category I]{C}[Category C]`. The FQN, mathematical premises and map values survived, but literal implicit public-signature preservation did not. Any broad earlier wording asserting that exact correspondence for this helper is withdrawn.

At generic `482a2e552bbc1cb016cd9c0817a1934e0751b9b713606ac737f5ed205368bba6`, the original explicit header and universe names are restored. The reviewer compared the exact text from `def constantDiagramColimitIso` to the preceding `:=` byte-for-byte with the original Stalk preimage; equality holds (header SHA `0a90f61a625abc3d6f6289dfa5cff1f87e772a04f4da9fc1766c4976771f6915`). The author's correction packet is `adjacent-constancy/versions/v4/API-CORRESPONDENCE-CORRECTION.json`, SHA `25994104a48c8ceff568f11a7a1d3a2c549ba24bbf42e1642c6469e064d0d96e`. The narrow normalization/header delta was read as a dependency; it adds no comparison data or new proof route, and the left associativity derivation is unchanged.

Source-bound supplied evidence records generic482 passing in `remote-3d23cc492c9c445aa2166b621125ce68`, source `49b89ba48f386e3f1d581b7f85cd794b3c343f7540928ce142a73db328bb13a8`. The shared job exited 1 at a native boundary. Only that generic module pass is retained; neither a v2 pass nor whole-run success is inferred.

**Root normalization2 proof hunk is sound.** Fixed `PullbackCohomologyNormalization.lean` SHA `3fb1fd622aea0a1b40d3a17365666e07dcfdd9e32e0c39a2320f506de0390379`, at `native-colimit-leg-normalization-staging/versions/v2/after.lean:36–53`, keeps the original theorem header and maps byte-identical. It names the literal original pullback value z at `H.{e}(C.obj_i)n`, applies native `H.map_comp_apply` directly, and composes with congrArg of the same original colimit-injection equation. This is the same previously reviewed proof route with explicit native value types. No Hom-ext surrogate, new morphism, model or premise enters. Its own native check remains pending; failed b36 rewrite encoding is historical.

Later `PullbackLimitCoefficient` `fdbfd365…` proof repairs are **not inspected here**. Their reported passes do not extend the fixed v2 source review or make this a verdict on the full current constancy packet. The normalization hunk is reviewed against the original injection theorem and retains that explicit dependency boundary. No new build, probe, audit or source/Git mutation was performed.

## Retained fixed-v2 review and history

The following prior report is retained as history. Its broad helper-signature statement is subject to the explicit withdrawal above; its mathematical verdict and original source vector remain unchanged.

---

# Current affected-source reconciliation: cone constancy v2

The mathematical verdict is **retained as sound** on current generic `ConeConstancy.lean` SHA-256 `097432f26253e8e4d4c1fcbdfbb5ba0aa7b6ff585992aebae05b680e5cb9f9d3`, with unchanged Scheme `DiagramLimitCoefficients` `fb0b4a66…`, `PullbackLimitCoefficient` `89e372f5…`, and root normalization `b36f5a05…`. Exact current sources are named in `adjacent-constancy/versions/v2/READY-applied.json`, SHA-256 `4584f8636460651125c9ee7b5b25c0b2cc1ed433c020b8cb0cd8504f0b29bb5b`, and in the JSON's full current vector. All three versioned images match N; root's unchanged fixed image remains the fourth target.

The v1→v2 delta only adds identity-component, right-identity and associativity normalization to two already reviewed triangle proofs, and exposes component compatibility as a locally proved hn before NatIso assembly. That hn is exactly `component_i.hom ≫ C.map a = component_j.hom`, proved from the same raw map formula and derived fixed-coefficient law. `Category.id_comp` followed by hn.symm then gives the native `NatIso.ofComponents` naturality equation. Compatibility is still proved, not an input. There is no change to any component, constructor data, public statement, world, hypothesis, actual colimit or insertion formula. The whole left-associativity derivation and connected-colimit comparison code are byte-identical.

The v1 native basis `2c50f914…` in run `a9f429be…`, source `8b43afd95d07964ede012580562b0c6bf195a3d3a859e7d26bb0bf87c2ef5d77`, has an own partial failure on those proof-normalization steps; the coupled native two were unreached. Independent grouped work may still be live. This is not relabeled as a v2 result or a whole-run exit. Current v2 elaboration remains pending with the author/compiler owner. No new execution/check gate or established status is introduced.

## Retained v1 derivation

The v1 mathematical derivation below is retained unchanged; its source/status statements are historical. Its report hashes before this continuation were MD `ae687f17ca295364606cce00f52791e4c4d161303f8bf3a31249cbd18c592be6` and JSON `4ea07d96838efef746036fd8d41a6be1fc5a0a60d1f76e4eb45cd147c6315f80`. The JSON preserves that prior record as well as the current source vector.

---


# Ordinary source review: continuity cone constancy

The fixed **COMPLETE3 v1 plus normalization1** sources below are **mathematically sound on the stated conditions**, with native elaboration pending. No mathematical/source-API blocker was found. This is an independent ordinary milestone review; no established status is assigned.

| Fixed source | After SHA-256 |
|---|---|
| `Aglib/AlgebraicGeometry/EtaleCohomology/Continuity/DiagramLimitCoefficients.lean` | `fb0b4a66a052bce297e0a43bc1bffcf9da1abe5eba306e583d3c8520d2e7cd29` |
| `Aglib/AlgebraicGeometry/EtaleCohomology/Stalk/PullbackLimitCoefficient.lean` | `89e372f533d9f9c1e82eb82eed23139319042aa3c40ee4dbe55ed1fd96c46dc4` |
| `Aglib/CategoryTheory/Sites/SheafCohomology/Continuity/InjectiveDiagram/ConeConstancy.lean` | `2c50f9149248601981e9b0818ebaacd430cbc8acfe3faadef626f6c885b20073` |
| `Aglib/AlgebraicGeometry/EtaleCohomology/Stalk/PullbackCohomologyNormalization.lean` | `b36f5a050be42ff4748c1f6c3c743e267eac7de08056947c8d7f0dcb9842546b` |

All four immutable afterimages match their supplied SHA-256 values and current N bytes. `R = /Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025`, `N = R/aglib`, native HEAD `54d6974ace11bf7d197aa925cb8cade86db8a24f`, entry HEAD `56a07882f536a20bfbbfeed42c9adb5fe74ef9e9`. Lean is 4.34.1; mathlib is `d13f23b723b8a846827a245b89c10fc7d3f11612`. The fixed packets are:

- `continuity-cone-adjunction-core-staging/adjacent-constancy/versions/v1/READY-applied.json`, SHA `c2f9441ce5df16f317cdc5bf91aff4a576961058b23f12f7ee01c2be0d9056ba`;
- `native-colimit-leg-normalization-staging/READY.json`, SHA `7ac028f568b5512f3ae0870a5b7920276b6bbdd0b96b208a5e1b928f945d6a51`.

Each existing-source preimage was read and equals the corresponding immutable `migration/audit-basis/aglib` source:

| Original existing source | Before SHA-256 |
|---|---|
| `Aglib/AlgebraicGeometry/EtaleCohomology/Continuity/DiagramLimitCoefficients.lean` | `e6066cf4832afb4c74c6c7ba8c43ef823eb91309cb39285f2d8e469555626f8c` |
| `Aglib/AlgebraicGeometry/EtaleCohomology/Stalk/PullbackLimitCoefficient.lean` | `ec9c58acd7a7e38b3be9631295a2af629569c5e72ba888e4cc83aa20016680f0` |
| `Aglib/AlgebraicGeometry/EtaleCohomology/Stalk/PullbackCohomologyNormalization.lean` | `ea30cb3d43e2de5833217c55824c5ad5d23404dd2354f44c5e9308c3e09b1a81` |

The companion JSON binds all fixed paths, dependencies, conditions and source identities. Earlier C1 four-source coverage is retained, without reopening the unchanged derivation.

## Original coherence supplies the full triangle argument

`ConeConstancy.lean:31–49` defines the left triangle by the original `D.leftCompIso` and the explicit transport for f≫q=p. Its right triangle is the original inverse right compositor with the same equality transport. The equality with the native canonical left comparison is proved, so it does not assume an alternative compositor.

At `55–97`, the precondition for native `Adjunction.leftAdjointCompIso_assoc` is proved from the existing `D.Coherent.inv_assoc`. In particular, its right comparison e is the actual compositor followed by transport along the reverse associativity equality. Taking inverse components gives the stated **whole left associativity** equation, including the forward `eqToHom` on the left-functor object. This matches the native theorem's orientation; no desired left coherence is a new premise.

At `99–135`, coefficient triangle composition keeps arbitrary original φ and ψ. The proof uses that whole associativity equation and naturality of the actual compositor, then appends the original mapped coefficient arrows. At `139–177`, structural triangle composition gives the fixed-coefficient component equation after composing with the original inverse triangle and cancelling the same isomorphism. At `181–194`, extensionality gives the whole natural-transformation equation with the original associator direction. These arguments establish the compatibility subsequently used to assemble constancy.

## Constancy uses the supplied actual diagram

`fixedCoefficientIso` at `196–225` receives one actual functor C. Its hobj and hmap state the literal object and triangle-transition formulas, with only the required equality transports. They do not state the desired structural-component naturality or constancy. The component at i is the actual triangle from L_l(F) to L_ci(L_bi(F)), followed by the supplied object-equality transport to C_i. The proved fixed-coefficient law establishes naturality; `NatIso.ofComponents` then assembles those original components.

The Scheme application in `PullbackLimitCoefficient.lean:103–123` sets C to the existing `coneCoefficientFunctor Y c (pullbackCoefficientSystem Y b F)`, rather than constructing another diagram. Its object equality is rfl. Its map proof unfolds the actual inverse transition supplied by the original `System.ofLeft` construction and rewrites it to the original `pullbackCoefficientTransition`. The new `pullbackConeCoefficientIso_app` at `125–134` proves equality of the whole component iso with the old `pullbackConeCoefficientComponent`; this also fixes the inverse-component value.

The generic coefficient categories keep uA/vA, the base category keeps uJ/vJ, and the index keeps uI/vI. The cone and cocone live in the actual base category, and l/hl are the original commuting data. No connectedness is required for this NatIso. No new Ext, injectivity, enough-points, geometric or size premise appears.

## The connected colimit has the original object as apex

At `ConeConstancy.lean:233–249`, `constantDiagramColimitIso` compares the original selected colimit of D directly with A. The target is the native `constCocone I A`, precomposed by e.inv using the native `IsColimit.precomposeHomEquiv`. Its apex is literally A. Native `isColimitConstCocone` supplies the colimit proof under the original `IsConnected I`; only `HasColimit D` is otherwise needed. The insertion equation is literally
`colimit.ι D i ≫ comparison.hom = e.inv.app i`.

The theorem at `253–267` proves equality of the **whole isomorphism** to the former expression `HasColimit.isoOfNatIso e.symm` followed by the selected constant-colimit comparison. It uses `Iso.ext` and `colimit.hom_ext`, the two literal insertion laws, and the native constant cocone's identity leg. This is stronger than an endpoint-isomorphism assertion and establishes correspondence with the old construction. The new constructor avoids selecting a second constant-diagram colimit apex.

The public `CategoryTheory.Limits.constantDiagramColimitIso` name and meaningful independent index/category worlds survive its move to the lower owner. Its old Stalk import closure still provides it; there is one implementation. The new Scheme limit coefficient iso at `143–158` uses this helper, the same actual coefficient functor, and the original structural components. Its original `ι_pullbackLimitCoefficientIso_hom` statement and inverse-triangle value remain unchanged.

## Original Scheme image maps and root normalization

`DiagramLimitCoefficients.lean:21–38` proves that the generic whole left compositor and triangle are the original `inverseImageComp` and `pullbackTriangleIso`. The proof uses injectivity of the actual native conjugate equivalence; it retains the original inverse/direct-image adjunctions and equality transport. The actual `triangleCoefficientMap` data at `40–45` is byte-identical to the original, and its composition statement retains the same arbitrary coefficient arrows and Scheme equations. The old Stalk private component/NatTrans statements and the public structural component/transition formulas remain, with thin generic proofs.

For root's `PullbackCohomologyNormalization.lean`, the entire theorem header and all map data are byte-identical before/after. At `36–43`, the proof applies extensionality, rewrites the two original nested H.map applications by native `H.map_comp_apply` in reverse, then applies the original coefficient insertion equation. The resulting coefficient map is exactly the original inverse triangle in `cohomologyTransfer`. No intermediate comparison, colimit, pullback map or Ext model changes. The independent Ext e and original stage/apex HasExt and colimit hypotheses remain.

The nontrivial prose claims in the new module—coherence-derived triangle composition/constancy, one supplied actual diagram, actual constant apex, and whole former-construction equality—are supported by these source derivations.

## Evidence boundary

All necessary native suppliers were inspected at the pinned sources, including `CompositionIso.lean:170–184`, native connected constant cocones `Connected.lean:56–94`, native colimit transport/uniqueness and `SheafCohomology/Basic.lean:135–145`. Full hashes appear in JSON. No build, probe, lint, test, axiom audit, replay, network or Git mutation was performed by this reviewer. Only the assigned review pair is written; prior reviews and foreign source work are preserved.

The four exact targets are selected in active run `remote-a9f429bedd3d4a9291f100c210a71ffa`, source content `8b43afd95d07964ede012580562b0c6bf195a3d3a859e7d26bb0bf87c2ef5d77`. No current native result is assumed. Elaboration and any coupled repair remain with the authors/compiler owner; later fixed repairs need only affected-source reconciliation.

The later square9 preparation, queued C2 delta, whole continuity theorem, full-family acceptance and established status are outside this verdict.

