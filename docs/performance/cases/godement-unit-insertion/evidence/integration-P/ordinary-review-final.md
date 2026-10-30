# Ordinary review: final modular Godement unit-span family

**Verdict: ACCEPT the identified final modular family's mathematical derivation and original-source correspondence, retaining every stated premise.** I found no unresolved mathematical obligation in this bounded family. Matching per-source native compilation coverage is supplied for all eleven reviewed files. This is an ordinary review, with no established-status decision, broad package/audit/CI conclusion, or controlled performance conclusion.

I remain independent of the construction and its repairs. I launched no Lean compilation, check, client, replay, or runtime job and changed no production source or Git state. Read-only source hashing, declaration comparison, and existing receipt inspection support the correspondence judgments below. Only this successor report was written.

## Basis, successor scope, and exact identity

Define:

- `Q = /Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/ci-etale-abstract-20261029`.
- `G = /Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/ci-repair-20261030/godement-optimization`.
- `D = G/split/final-delivery`.

`Q` HEAD is `7d071440653407d30fd41d8dbbafce1673a3039b`. The original native beforeimage remains SHA-256 `48cabc494c9aba779b667c5b6fc4d4b235fae3af40c5479ddf25a5be273867f3`. The unchanged `UnitInsertion` provider remains `7da85dc12042849006c8baa2c847c7ab87d13c844e488d34c8a96692ff7bfc7b`.

The principal explicitly resumed the same ordinary family review on this final modular basis. The previous `REPORT-v2-v3.md`, SHA-256 `b76ca2e7a20b9a3f4d4889a35cf38a7c2ca9b1ca2dfa56813614e3c4dc514b47`, is unchanged and remains a verdict on its own source bytes. Its monolithic native proof route and pending-compilation statement are historical. The current proof route and compilation coverage below apply to the new modular vector; no old execution is relabelled as this phase.

All eleven current `Q` files, their immutable `D/source/after/` copies, `D/SOURCE-VECTOR.json`, and the corresponding rows of `D/CPP-COVERAGE.json` were reconciled by exact hashes. No drift was found.

| Source relative to `Q` | SHA-256 |
|---|---|
| `Aglib/CategoryTheory/Functor/NatTrans/UnitInsertionSpan.lean` | `84bdff5cea154b04a0f2df6429e2ba6505034a7831c0620521da33dd30c62342` |
| `Aglib/AlgebraicGeometry/Cohomology/Godement/OpenBaseChange/Basic.lean` | `a3c32be2f1ef4768b058dc006c5c79446b643a6d298f2967a99858839142ead0` |
| `.../OpenBaseChange/Geometry.lean` | `8b2bb306df1a7fc007f2c37e7eb52146e7d3858c7d314b63122cef0708a48537` |
| `.../OpenBaseChange/Bridge.lean` | `ed96fbf7d031ec78c541d5eabdb225e8b98efeb884df7a1ba147597abcc0fd47` |
| `.../OpenBaseChange/SpanData.lean` | `3241adae150f33d252df65728316fa92ed5613387ef79caa63844188f17821df` |
| `.../OpenBaseChange/FirstSquare.lean` | `f5b264357254605e1124c194f7b2c31e3d9af87779502a7fdecbb76263f6bb94` |
| `.../OpenBaseChange/SecondSquare.lean` | `0017416d20d1bf61a6d3f3d152e7f184a0a497134dbae605ead5241b8ee1ee1d` |
| `.../OpenBaseChange/SpanComponent.lean` | `c4da49721d261a5623feac69ec09e6e5a705705fec2d608eaf002a8ee2e7090f` |
| `.../OpenBaseChange/SpanFactorized.lean` | `05927d624a8ec60b52a25efefcdd2ca52eb0b4b334e8769f319102f0d88c6254` |
| `.../OpenBaseChange/Span.lean` | `b1cd0df977d580645d71aaa6a884a2b3e79e16de66ad8863fd312b7441e57f20` |
| `Aglib/AlgebraicGeometry/Cohomology/Godement/OpenBaseChange.lean` facade | `d0594d133f27d56747f5a0daeaab4cd296e533e6137dd2df8ce9f069f69f5871` |

Packet identities are `D/SOURCE-VECTOR.json` = `2f7ad689b7ecd6453e70529ec6e5d77ae9f1f7b11ec482944bdfebafe3e0c778`, `D/SOURCE-CORRESPONDENCE.json` = `428ce0d1c76ff8b198fad449b93686b2bbccf30b080e5dbeeb705ac2f6c0b2a5`, `D/CPP-COVERAGE.json` = `9014669671b044577c39ae75b655ebc4874c110ae910bf8051079442ed1c73d5`, and `D/RESULT.json` = `d2411127402e6a22f5ea05da5d476afa25a9b2e34ed56c65c4c664cd3f4c3473`. The author return `G/split/span/FINAL-RESULT.json` is `accc0cd4a5f9fe7436d10bf1772e327fe3872528be7a57204350b82dc074c0e7`.

## Lower construction and uncovered additions

The original lower construction through line 113 is unchanged from reviewed `285026f...`. Retained ACCEPT coverage therefore applies to `UnitInsertionSpan#unitInsertionBridge`, `#unitInsertionBridge_app`, `#unitInsertion_first_square`, `#unitInsertion_second_square`, `#unitInsertion_span_factorized`, and `#unitInsertion_span`, with the independent geometric unit equation `hη` retained for the first and whole squares. The bridge remains literally `β` followed by `T.map δ`; comparison naturality and augmentation naturality supply the two squares.

The new lower claims were read and independently assessed as follows. Identifiers are in `CategoryTheory.NatTrans`.

| Result | Conclusion and premises | Verdict |
|---|---|---|
| `UnitInsertionSpan#unitInsertion_first_square_app` (115) | Evaluation at arbitrary `K` of the proved whole first square gives `(Sη ≫ (R⋙S)δ) ≫ α = η' ≫ R'B`, retaining `hη`. It is `congrArg (fun γ => γ.app K)` before any native substitution. | ACCEPT |
| `UnitInsertionSpan#unitInsertion_second_square_app` (126) | Evaluation at arbitrary `K` gives `R'B ≫ R'ε = R'ε ≫ R'H(B)`. It projects the proved whole second square. | ACCEPT |
| `UnitInsertionSpan#unitInsertion_span_factorized_app` (136) | Evaluation gives the complete factorized pointwise span, retaining `hη`. It projects the proved whole span. | ACCEPT |
| `UnitInsertionSpan#unitInsertion_first_square_point` (153) | For `α : F₁ ⟶ T⋙R'`, an arrow `δ : A ⟶ B`, and `hunit : u ≫ α_A = v ≫ R'β`, naturality of `α` gives `(u ≫ F₁δ) ≫ α_B = v ≫ R'(β ≫ Tδ)`. Only this arrow, the three functors, comparison, and independent unit equation are needed. | ACCEPT, with `hunit` |
| `UnitInsertionSpan#unitInsertion_first_square_point_map` (164) | Applying an arbitrary actual functor `P : E ⥤ Z` to that already-proved square gives its displayed evaluated factors, by `P.map_comp`. The evaluation proof is made with all categories, functors, and arrows variable. | ACCEPT, with `hunit` |
| `UnitInsertionSpan#unitInsertion_span_point` (176) | The first square and naturality of `ε : 𝟭 F ⟶ H` give the full pointwise span. `hs : s = β ≫ Tδ` specifies the original bridge value; it is not the final span equation. | ACCEPT, with `hunit` and `hs` |
| `UnitInsertionSpan#unitInsertion_span_point_map` (195) | Applying `P` to that complete span and using functoriality gives its evaluated factorization. | ACCEPT, with `hunit` and `hs` |
| `UnitInsertionSpan#unitInsertion_map_span_eq` (210) | An already-proved abstract span `h` is transported through `P`, with the displayed associations. This is a conditional functoriality law; it does not prove its input `h`. | ACCEPT within that explicit conditional scope |

The last transport lemma supplies no circular premise to the native proof: the final native chain uses the first-square point-map law, the independently proved original augmentation square, and generic categorical pasting. The lower point interface avoids unnecessary adjunction, total-functor, derived-category, or geometric data. The original four object/Hom universe pairs remain independent, and the evaluation target has its own independent `uZ/vZ` pair. No realization or replacement category is introduced.

## Native derivation and claim-specific correspondence

The current assembly has the following source-level route. All leaf locations below refer to the exact vector above.

| Result | Mathematical conclusion and decisive correspondence | Verdict |
|---|---|---|
| `OpenBaseChange#open_geometric_unit` (`Geometry`, 56) | The original geometric adjunction unit commutes with the original pushforward comparison and pullback mate. Its original proof reduces to `cartesianOpenBaseChange_pullback_unit` in each degree; it contains no Godement augmentation or final-span premise. | Retained ACCEPT |
| `OpenBaseChange#open_component_first_square` (`FirstSquare`, 32) | The exact original degreewise first square is obtained from `unitInsertion_first_square_point_map`. Here `F₁ = push_f⁺ ⋙ restrict_j⁺`, `T = restrict_a⁺`, `R' = push_b⁺`, `α = openPushPlusIso.hom`, `δ` is the actual Godement augmentation at `pull_f⁺ K`, `u,v` are the original geometric units, and `β = openPullPlusIso.hom.app K`. `hunit` is exactly `open_geometric_unit ... K`. The evaluation functor is the actual `CochainComplex.Plus.ι V.Modules ⋙ HomologicalComplex.eval V.Modules (.up ℤ) n`. Thus the generic evaluation theorem is proved before these native inputs are supplied. | ACCEPT |
| `OpenBaseChange#local_total_unit_component` (`SecondSquare`, 47) | The original bridge commutes with the original augmentation in degree `n`. The generic private `augmentation_component_naturality` is applied to the actual bridge and original `godementTotalPlusUnit W`; `openTotalBridge_f` supplies its actual two factors. The private lemma and this full public declaration are byte-for-byte original `48cabc...`. | Retained ACCEPT |
| `OpenBaseChange#open_component_second_square` (`SecondSquare`, 66) | Pushforward of that original augmentation square is the exact original second component equation, by functoriality. The full public declaration is byte-for-byte original. | Retained ACCEPT |
| `OpenBaseChange#unit_span_pasting` (private, `SpanComponent`, 29) | In any category, `u≫p=v≫q` and `q≫r=s≫t` imply `u≫p≫r=(v≫s)≫t`. The proof uses only associativity and substitution; object/Hom universes are independent. | ACCEPT |
| `OpenBaseChange#open_unit_span_component` (`SpanComponent`, 44) | The two actually proved original component equations instantiate that categorical pasting law in the same ordinary module category. The conclusion is the original complete component span. No whole-span theorem is an input. | ACCEPT |
| `OpenBaseChange#open_unit_span_factorized` (`SpanFactorized`, 31) | The original full-Plus factorized equality follows from equality of its underlying complex maps in every degree: `ObjectProperty.hom_ext`, `HomologicalComplex.Hom.ext`, then the preceding component theorem. This is the original faithful-inclusion/extensionality proof on the same maps. | ACCEPT |
| `OpenBaseChange#open_unit_span` (`Span`, 32) | The original resolved unit satisfies the original complete native span. Its original unit-factor rewrites and proof are unchanged. | Retained ACCEPT |
| `OpenBaseChange#pullbackPushforwardPlusUnit_restrict_quasiIso` (`Span`, 43) | For the original cartesian/open context and local quasi-isomorphism hypothesis `hK`, restriction of the original global resolved unit is a quasi-isomorphism. The original span-cancellation proof consumes the same comparison and the same two quasi-isomorphic legs. | ACCEPT, retaining `hK` and original context |

The native whole equality is now assembled from the proved components through original extensionality. Descriptions of a generic evaluated span in the leaf prose are justified by this assembly; the actual route above is the source-correspondence statement for this version. The first and second native squares are not supplied as new theorem hypotheses.

## Preserved values, premises, models, and module dependencies

Independent declaration comparison found exactly **29 original public names, each once, with all 29 headers unchanged**. Twenty-eight full public declaration texts retain the original token sequence; the sole changed public proof body is `open_component_first_square`. All eleven native definition/abbreviation bodies are unchanged: the two comparison isomorphisms, bridge, restricted/local complexes, restricted total, target, restricted unit, comparison, and both legs. Hence the original six pullback/pushforward/restriction functors, both Godement totals and augmentations, cartesian comparison, and pullback mate remain the actual values.

The unchanged stable suppliers were read in their new leaves and reconciled with the earlier review. In `Basic`, `Plus#pushforward_quasiIso_of_flasque`, `#quasiIso_of_isIso_Q_map`, `#quasiIso_of_span`, and `Godement#totalPlus_terms_isFlasque` retain their original conclusions and proofs. In `Bridge`, `#openTotalBridge_quasiIso`, `#restrictedTotalPlus_flasque`, and `#openTotalBridge_f` retain their original conclusions and proofs. In `SpanData`, `#restrictedPullbackPushforwardPlusUnit_factor`, `#openBaseChangeGlobalLeg_quasiIso`, and `#openBaseChangeLocalLeg_quasiIso` retain their original factorization and quasi-isomorphism conclusions. ACCEPT coverage is retained for these exact unchanged dependencies and their current uses, over the assignment's accepted original upstream background.

Original scheme universe `u`, maps `a,b,f,j`, open immersions `a,j`, cartesian hypothesis `h`, lower-bounded complexes, arbitrary integer degrees, flasqueness conditions, and final `hK` remain. No Flat hypothesis, bound, coefficient, world identification, or site/topos presentation is added, removed, or narrowed. The only two `HasDerivedCategory.standard` constructions in this family are the original named constants in `Basic`:

- `AlgebraicGeometry.Scheme.Modules.Plus.openBaseChangeDerivedStandard`;
- `AlgebraicGeometry.Scheme.Modules.Godement.openBaseChangeDerivedStandard`.

Other relevant leaves enable the same existing Godement value locally. `Geometry` and `FirstSquare` declare or select no new derived model. This statement concerns the adopted family; it does not assert that unchanged transitive providers contain no derived-category declarations.

The import graph is acyclic: `Bridge ← Basic,Geometry`; `SpanData ← Bridge`; `FirstSquare ← Geometry`; `SecondSquare ← SpanData`; `SpanComponent ← FirstSquare,SecondSquare`; `SpanFactorized ← SpanComponent`; `Span ← SpanFactorized,SpanComponent`; the facade publicly imports `FirstSquare,SecondSquare,Span`. The three private helpers are used only inside their own files: flasque pushforward in `SpanData`, augmentation naturality in `SecondSquare`, and categorical pasting in `SpanComponent`. No private cross-file dependency is missing. The facade adds no declarations and exposes the original public family through public imports.

All source options are the same two original backward-definitional-equality options scoped to the respective leaves. No axiom, `sorry`, `admit`, budget increase, or linter/trust relaxation is introduced in these proof sources. This source assessment is not a transitive compiled axiom audit.

## Compatible execution evidence and remaining boundary

I reused the supplied native compilation evidence, matching every covered module's hash against the reviewed current file and immutable snapshot. The native pins remain `lean-toolchain` = `d5edba4e4b8faad9c1baeadb265716d20d03be4d1a2647dc5e35b0c0325bea7b`, `lakefile.toml` = `74dd001400a84f17bd496d0b490cd72f4ab75455961ca2cd75bab5903990d852`, and `lake-manifest.json` = `4b56d1e50c168c3ab7816447e7f98da2584f9d509825422c22afaf48ab1ebea2`.

- `remote-f0e024e250804c8d979a57763b374078` / `SOURCE4c06...` supplies six source-specific successful modules: common, Basic, Geometry, Bridge, SpanData, and FirstSquare. That mixed group failed overall; only these matching successful module outcomes are retained. The actual first-square frontend completed in 13.671894 seconds.
- `remote-aea9cae634c24e6d9323eb65ce15d43c` / `SOURCE1d49...` supplies the exact restored SecondSquare pass.
- `remote-5c803ce865cb4c8aad12a9ba6412f841` / `SOURCEe778...` supplies the exact SpanComponent pass.
- `remote-f5e90209372b4bfbace5da3e7dc12d01` supplies the exact SpanFactorized pass on `SOURCEe9ad...`.
- `remote-dc117035f822435c959fbae836ff2c8d` supplies Span and facade on the same final `SOURCEe9ad8c9d8096784793242fecf0712f2d18fdef19c8cde5eece836e90a55f46ff`; the two actual compiler invocations finished with exit 0 and no input drift. The facade success reuses matching successful dependencies. The phase duration is 307.515472 seconds; this is not a cold-build comparison.

The full final source manifest is `G/../../source-manifests/continuation-A-Q7d-e9ad-faithful-factorized-f5e90209.json` as resolved by the absolute locator in `D/SOURCE-VECTOR.json`; its verified SHA-256 is `2e1c6c972e3cbeda9c478f7b59748d366bd7af1419b9889a3d65cb8a14d5cd63`. `D/CPP-COVERAGE.json` owns exact source/run/receipt/event/log locators. Existing selected final receipts were also inspected directly: status succeeded, exit 0, closed groups, and empty drift lists.

No mathematical or identified proof-compilation gap remains in this assigned vector. Root retains source integration into any different checkout, native aggregate adoption/checks, existing affected audit predicates, package/style/tests and hosted CI boundaries. Newer P/remote changes, policy/docs and PERFORMANCE proposals are outside this proof verdict. Neither this review nor the supplied CPP establishes whole-Aglib/whole-Etale closure, a cold-build speedup, a unique cost cause, or established exposé status.

For correspondence reproduction, inspect `D/SOURCE-VECTOR.json` and hash its eleven current/snapshot paths; the original beforeimage is `G/production-integration/before/Aglib/AlgebraicGeometry/Cohomology/Godement/OpenBaseChange.lean`. Normal incremental compilation, if subsequently warranted by changed inputs, is `lake build +Aglib.AlgebraicGeometry.Cohomology.Godement.OpenBaseChange` in `Q`; the existing matching coverage needs no rerun for this report.
