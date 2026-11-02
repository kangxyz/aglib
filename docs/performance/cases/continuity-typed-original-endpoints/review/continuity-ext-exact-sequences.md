# Current affected-source reconciliation: C2 v5

The complete-common-proof verdict is **retained as mathematically sound** on the exact current **v5** vector. Only two generic proof encodings change from the reviewed v4 derivation; no mathematical or source-API blocker was found.

| Current source | SHA-256 |
|---|---|
| Generic `RepresentedDiagram/ExactSequences.lean` | `e8b24314038d875cf9926b4035813322fd603351baeba6bb3284af1a2ed7018c` |
| Scheme `DiagramCokernelTransitions.lean` | `318544c51a055a1d0b8c05aa7aa047086ef52c32edccf1dce8d02e8839835c8d` |
| Scheme `DiagramCohomologyConnecting.lean` | `39056a2efc0dec8305d403670ad2e6ba2a4562bd0754d0488a4e77ad0202b315` |
| Scheme `DiagramCohomologyExact.lean` | `6ce27e8c93ac2acb63b1775a6ecab31d3a2ab9869189823167eeff9c043b631e` |

The immutable images are named by `continuity-ext-exact-sequences-staging/versions/v5/READY.json`, SHA-256 `6b3bb25c7fe5471e3e130bd7fb1cd02947230adb4705b54b45823d91ce753c1e`. The three Scheme images are byte-identical to v4. The v4 and v2 source vectors, mathematical coverage and actual execution boundaries remain preserved below and in the JSON; their statuses are historical.

The first changed `comm₁₂` proof proves the same original Ext-element equality as a local `h (x : Ext X T.X₂ n)` before applying `ext x; exact h x`. Its native Ext transport, degree-zero coefficient composition and α.comm₂₃ calculation are unchanged. The second changed `comm₁₂` proof first proves the same explicit original-arrow equality
`p₂ ≫ Ext.map(S.g) = colim.map(original coefficient transformation) ≫ p₃`
by the already reviewed colimit-injection argument, then supplies it by `exact h` to the unchanged row field. Both h facts are proved locally. Neither becomes a premise or replaces an original map with an inverse-Hom/model reconstruction. The changes only expose native row projection types before proof elaboration; all statements, data components, source/target/Ext worlds, original colimit choices and conditions are unchanged.

The actual v4 native run `remote-8b24d37a2ea243c19ee9adf287a50923`, source content `ac3d9eb5bd7817ea22856d7c567ee6d82d12a0330d3536f53beb696739a6f991`, failed on generic `0ab90cea…` rewrite transparency; its three Scheme modules were unreached. That failure is retained on v4 and is not a v5 result. Current v5 compilation remains pending with the author/compiler owner. The old `6aec3df9…` pass also remains old-basis only. No new compilation, probe, tests, audit or source/Git mutation was performed by this reviewer, and no established status is assigned.

## Retained v4 derivation and v2 history

The following v4 report is retained verbatim (SHA-256 `d39bd2fa774d00ef66a9bc374b4d36a7cdc03ab2dad39861acc9cf54ec997ed8`). It contains the retained v2 review. Its then-pending v4 execution status is superseded only by the precise v4 failure/current v5 boundary above.

---

# C2 affected-source continuation: complete generic row assembly

**Current verdict:** the fixed **v4** sources below are mathematically sound and preserve the original Scheme maps, statements and conditions. The complete common Ext-row and colimit-square argument is now generic. No mathematical or source-API blocker was found. All four images are applied; native elaboration of this extended vector remains pending. This is ordinary source review, not established status.

| Current fixed v4 source | SHA-256 |
|---|---|
| `Aglib/CategoryTheory/Sites/SheafCohomology/Continuity/RepresentedDiagram/ExactSequences.lean` | `0ab90cea208105e59bc4f109d4a5016e195dc08a340d5b62dbd0f9c9d8d14418` |
| `Aglib/AlgebraicGeometry/EtaleCohomology/Continuity/DiagramCokernelTransitions.lean` | `318544c51a055a1d0b8c05aa7aa047086ef52c32edccf1dce8d02e8839835c8d` |
| `Aglib/AlgebraicGeometry/EtaleCohomology/Continuity/DiagramCohomologyConnecting.lean` | `39056a2efc0dec8305d403670ad2e6ba2a4562bd0754d0488a4e77ad0202b315` |
| `Aglib/AlgebraicGeometry/EtaleCohomology/Continuity/DiagramCohomologyExact.lean` | `6ce27e8c93ac2acb63b1775a6ecab31d3a2ab9869189823167eeff9c043b631e` |

The review question is the material continuation specified by `continuity-ext-exact-sequences-staging/versions/v4/READY.json`, SHA-256 `69eef621db297823a73ba9bba1021966b0a60af1a5548fed56f8652ec8f16a3f`. All four immutable snapshots match both READY and their current N bytes. Native HEAD remains `54d6974ace11bf7d197aa925cb8cade86db8a24f`, with Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. All 21 previously bound load-bearing dependency files retain their hashes. The companion JSON preserves full identities and the earlier v2 review record.

## Complete common derivation

At `ExactSequences.lean:103–132`, `extPrecompMap_connectingComplexHom` takes the actual exact additive functor L, original source arrow a and actual short-exact sequence morphism α. It maps the row
`Extⁿ(X,T₂) → Extⁿ(X,T₃) → Extⁿ⁺¹(X,T₁)`
to the same native row for V and S. Its three components use α.τ₂, α.τ₃ and α.τ₁ in that order, each after the original `L.extPrecompMap a`. This permutation is exactly the row order. The first square follows from the native coefficient composition laws and α.comm₂₃; the second is the reverse of the already reviewed connecting-naturality equation. No replacement Ext group or desired row-law premise is added.

At `208–238`, the new colimit-connecting theorem takes the original comparison arrows p₁ and p₃ and literal equations for their values after every colimit injection. Write mᵢ for the actual stage Ext-row morphism. The hypotheses say only
`ι_F,i ≫ p₁ = mᵢ.τ₃` and `ι_coker,i ≫ p₃ = mᵢ.τ₂`.
They do not assume the final connecting equation. After precomposition by `ι_coker,i`, the claimed equation becomes
`δᵢ ≫ mᵢ.τ₃ = mᵢ.τ₂ ≫ δ_S`,
which is precisely the proved stage row square. `colimit.hom_ext` then proves the original whole comparison equation.

At `240–272`, `representedCohomologyConnectingComparison` constructs the complete row morphism with components literally p₂, p₃ and p₁. The first square is also proved by `colimit.hom_ext`, the actual injection-value equations and mᵢ.comm₁₂. The second uses the generic colimit-connecting theorem just described. Thus both universal-property square proofs are below Scheme; the Scheme files supply actual maps and their original leg equations. No capability containing the desired final connecting/row law, new carrier, or second comparison construction appears.

The new `L_i` family is actual apex exact-functor data. Its source maps aᵢ and sequence morphisms αᵢ have independent apex/stage object and Hom worlds, with the one requested Ext e independent of them and of the index worlds. The generic comparison assembly assumes actual colimit existence in `AddCommGrpCat.{e}`; it does not assume `HasExactColimitsOfShape`. That latter hypothesis remains confined to the exact-colimit theorem at `276–283`. There is no new injective-existence, enough-points, continuity or invertibility premise.

## Actual Scheme instantiation

The changed `DiagramCohomologyConnecting.lean:61–80` and `DiagramCohomologyExact.lean:77–94` use exactly:

- Lᵢ = the original `inverseImage (c.ι.app i).unop`;
- V = the original constant sheaf on `ULift.{u+1} ℤ`, with aᵢ the inverse of `inverseImageConstantIso`;
- S = the original `coneCoefficientColimitCokernelComplex`, with its genuinely proved short-exact certificate;
- αᵢ = the original `diagramCokernelLimitLeg`, whose three components remain the original coefficient `colimit.ι`;
- p₂, p₃, p₁ = the original `schemeLimitCohomologyComparison` for Q in degree n, coker η in degree n, and F in degree n+1;
- the unchanged `ι_schemeLimitCohomologyComparison` equations as the actual leg normalizations.

Unfolding the native Ext-row components gives the original `cohomologyPullback` followed by the original coefficient injection: these are precisely the previously reviewed `diagramCohomologyLeg` arrows. The input leg equations therefore come from the old `colimit.desc` construction, not from the result now being proved. The final row morphism's three data components agree with the old record; only its Prop-valued square proofs move. All old public names, displayed statements and meaningful context hypotheses are retained.

The `DiagramCokernelTransitions.lean:37–43` encoding repair explicitly supplies an existing `PreservesZeroMorphisms` instance for the actual inverse image. It leaves all three transition maps unchanged and adds no public assumption. Its `evaluationToColimit` leg at `48–51` is unchanged. Pointwise monicity, stage/apex HasExt, coefficient-value colimit existence and genuine filtered coefficient exactness remain as before. The original `AsSmall`/`ULift` exact-colimit bridge in `DiagramCohomologyExact:44–50` is byte-identical; the new assembly neither collapses worlds nor derives continuity from AB5.

## Dependency and execution reconciliation

The actual C1 dependency now has generic Cone `dd35d1ef…`, `DiagramLimitFunctor` `78eeba5e…`, `DiagramAdjointCocone` `f35ce7d0…`, and `DiagramAdjointFamilies` `6e6bdedc…`. All fixed images match N. Since the earlier C1 review, only the Cocone encoding additionally names the caller's existing HasColimit hF and binds **that same hF** at the definitionally identical generic functor type. The inspected delta retains the same colimit, injection and adjoint map. It introduces no new mathematical argument or model.

Existing C1 source-bound native passes are reused as dependency evidence: generic dd35 in closed successful `376370c0…`; LimitFunctor 78ee as a passed module in mixed failing job `3907b635…`; Cocone f35c and Families 6e6b in closed successful `9deaa408…`. Only the indicated module coverage is retained; the mixed job is not relabeled as successful. This reconciliation does not edit or reopen the earlier C1 review report.

The existing `cc085927…` native pass covers old generic `6aec3df9…` only. It does **not** cover extended generic `0ab90cea…` or this v4 vector. A redundant copy of the v2 compiler-result metadata initially present under v4 explicitly named v2/6aec; it was recognized as historical and subsequently removed by its author, with original v2 metadata preserved and no Lean/READY change. No current pass is inferred from that filename. Current v4 compilation is author/compiler-owner work and remains pending in this verdict.

No source, compiler, probe, lint, test, replay, axiom audit, network or Git mutation was performed by the reviewer. Only this C2 review pair is updated. Any subsequent fixed proof-critical delta requires affected-source reconciliation only. No full geometric continuity, comparison invertibility, full-family acceptance or established status is claimed.

## Retained v2 review

The following is the prior report verbatim, SHA-256 `462c215dbd27e796b9b3d3f2150d51fced19dc7416480026faa810543747a84b`, paired with prior JSON `1dbc71b978c8412ff75cf2dbec29bc88b28cdd2febc6b85a60dea15c84b75e95`. Its source/status statements refer to that historical v2 basis. The unaffected derivations and original-map correspondence remain retained; changed source and execution statuses are supplied above.

---

# Ordinary source review: continuity Ext exact sequences

This is the independent C2 review of the exact **v2** source vector below, with generic `ExactSequences.lean` at `6aec3df96c934a41446ff725b92faedf25294f503b7f085fb43778cbe2b768d7`. All four fixed snapshots match their supplied hashes. The mathematical/source-correspondence verdict is **sound on this basis**. Existing generic native coverage is retained separately; the three Scheme afterimages remain staged and require later elaboration. No mathematical blocker or established-status assignment is made.

| Fixed source | SHA-256 | Native status at identity binding |
|---|---|---|
| `Scheme Continuity/DiagramCohomologyConnecting.lean` | `f61e38ae13c760bcaff66bd78eb53861e54fe81c33567209a706e6dcc1209c4a` | staged, unapplied and uncompiled |
| `Scheme Continuity/DiagramCohomologyExact.lean` | `8592a26c9c482e9093af97e6bc0a6e792c17ddf29d530a10016ace20d405c512` | staged, unapplied and uncompiled |
| `Scheme Continuity/DiagramCokernelTransitions.lean` | `0554f68a4f5b4d7e05f57db2a293fed68377a05f02374dd94b7aeeb9a1f2588a` | staged, unapplied and uncompiled |
| `Generic Continuity/RepresentedDiagram/ExactSequences.lean` | `6aec3df96c934a41446ff725b92faedf25294f503b7f085fb43778cbe2b768d7` | new generic leaf applied |

Here `R = /Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025`, `N = R/aglib`, and the immutable original is `R/migration/audit-basis/aglib`. Fixed snapshots are in `migration/implementation/continuity-ext-exact-sequences-staging/versions/v2/`, as named in `SOURCE-READY.json` (SHA-256 `e8cd8d02b79aa71616e2452181e85895efb5f7e1bf7eff39b6b4d65de443b51f`) and `SOURCE-MAP.json` (`bf0c2809ce033fd225213f7d10ba6568650429f8e1777d374ffbf0cbc34df4c7`). Native HEAD is `54d6974ace11bf7d197aa925cb8cade86db8a24f`; entry HEAD is `56a07882f536a20bfbbfeed42c9adb5fe74ef9e9`; Lean is 4.34.1 and mathlib is pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Full source/dependency identities are in the companion JSON.

Native still equals the original Scheme preimages:

- `Scheme Continuity/DiagramCohomologyConnecting.lean`: `6e7461cad3431ec7d7cb51fad18576aa405c46b4e7c573e18bc36a7d501813a1`.
- `Scheme Continuity/DiagramCohomologyExact.lean`: `f1e54cbf49e1696e3c68dfcadf9609a590df8e3c793c8335fa48b9307c2a8c8b`.
- `Scheme Continuity/DiagramCokernelTransitions.lean`: `97d169aec1cb02e82b0ff49768b4f602bcda26774cf1e574ba1701d038fb0100`.

## Transitions, connecting value and exactness

At `ExactSequences.lean:113–121`, the coefficient-sequence morphism has exactly
`τ₁ = F.leftMap(a)`, `τ₂ = Q.leftMap(a)` and `τ₃ = (coker η).leftMap(a)`.
Its squares are the existing `System.Hom.leftMap_naturality` for `η` and the original cokernel projection. The staged `diagramCokernelTransition` at `DiagramCokernelTransitions.lean:37–40` specializes these same arrows: `diagramInverseTransition` unfolds to the same original inverse-Hom-equivalence map. The short-exact certificates at `125–129` use pointwise monicity of the given `η`, with the original cokernel and no injective-object premise.

The connecting component at `139–146` is literally
`δ_i(x) = x.comp h_i.extClass rfl`.
At `42–61`, naturality first uses the existing `Functor.extPrecompMap_connecting` for the given exact additive functor and original source arrow. Native `ShortComplex.ShortExact.extClass_naturality` for the actual three-component sequence morphism, followed by Yoneda associativity in the displayed degree-zero directions, gives the required square. `representedCohomologyConnecting` uses its reverse at `147–152`, exactly the natural-transformation orientation of the original coefficient diagram. No desired transition/connecting compatibility is a premise.

The row at `154–171` has the original quotient coefficient map as its first arrow and that connecting transformation as its second. Its zero certificate is from the native `Ext.covariantSequence_exact`; exactness follows from the native `Ext.covariant_sequence_exact₃'` after `ShortComplex.exact_of_evaluation`. The non-diagram apex row at `84–99` uses precisely the same two native arrows. These operations only use the existing selected Ext groups. Native theorem-internal derived-category arguments do not introduce a new caller-level model or hypothesis.

The generic colimit theorem at `173–180` explicitly requires both colimit existence and `HasExactColimitsOfShape I AddCommGrpCat.{e}`. Mapping the exact row by this actual `colim` proves exactness. It does not infer continuity or invertibility from AB5.

## Original apex assembly and public API

`ShortComplex.evaluationToColimit` at `74–80` has the literal three `colimit.ι` maps. The staged `diagramCokernelLimitLeg` at `45–48` applies it directly to the existing `coneCoefficientCokernelComplex`. Its evaluated source is the old short complex mapped by the old cone projection's inverse image, and its target is that same short complex mapped by `colim`. The original `DiagramShortExact.lean:58–71,116–129` supplies those exact object/map identifications.

The staged leg square at `DiagramCohomologyConnecting.lean:43–56` uses the original `inverseImage (c.ι.app i).unop`, the inverse of the original constant-integer transport on `ULift.{u+1} ℤ`, and this original coefficient colimit leg. Those are precisely the original `diagramCohomologyLeg` arrows by `cohomologyPullback` and `cohomologyTransfer`'s defining formulas. At `61–72`, `colimit.hom_ext`, `colimit.ι_map`, and the original injection normalization of `schemeLimitCohomologyComparison` assemble the square. The comparison itself is never assumed to satisfy the desired conclusion.

The staged `DiagramCohomologyExact.lean:63–85` retains the original constant integer sheaf and actual coefficient short complex at the apex. Its comparison morphism retains literally
`schemeLimitCohomologyComparison X c Q n`,
the same map for `coker η`, and the same map for `F (n+1)`. The original comparison data and all public names/displayed types survive; selected definitions become transparent abbrevs and proof certificates change only in Prop fields. Native `Sheaf.H`, `H.map`, and `H.δ` are definitionally the specified Ext groups, degree-zero postcomposition and extension-class postcomposition, so this is actual map correspondence, not an abstract isomorphism of endpoints.

This apex integration uses C1's actual coefficient functor and literal legs. C1's initial reviewed producer `f40b6f…` is reconciled to the current `dd35d1ef3e6e16aea1e4c9c5e1f93cf5f7573feb63e0f099be692b36416cfd5c` by a private transport-normalization hunk; its coefficient-functor data and staged `DiagramLimitFunctor` `78eeba5e…` are unchanged. Both fixed bases are retained in `continuity-cone-adjunction-core.md`; that review does not assume a continuity comparison. C2's stage-only generic producer is independent of C1.

## Worlds, premises and evidence limits

The generic source/target categories have independent object/Hom universes `uC/vC` and `uB/vB`; the stage/index universes are `uA/vA/uI/vI`. The requested Ext `e` remains independent of all of them. One shared `e` is used for the categorical Ext diagram, matching the original Scheme API. The older `extPrecompMap_connecting` with independent `w/w'` remains unchanged; this new row does not narrow it.

All original Scheme `u/e/uI/vI`, stage/apex `HasExt`, pointwise monicity, filteredness and colimit-existence assumptions remain. The local additive/exact/cartesian instances only expose already proved properties of the original image/source functors. The private `exactCohomologyFilteredColimits` body at staged `44–50` is byte-identical to the original: `AsSmall.{max e uI vI}` changes the indexing presentation for the exact-colimit proof and `AddCommGrpCat.uliftFunctor.{max uI vI,e}` transports exactness back to the original value category. Native ULift preserves actual-shaped colimits and preserves/reflects finite limits. This retains independent index/Hom worlds; it is not a new cohomology carrier or an AB5-only continuity proof.

Existing native receipt `remote-cc085927969c40b28f87039de26e488b` covers only generic `6aec3df9…`: source content `ee57c2bccc386a5908c75a428ae6d2a0dc91c9c3a6b6f1fcb38f3460ecdddcd6`, source-manifest SHA `dc7c5640d5caaab942e3078c56865db8c4825c93bc1380a0c59ff531fa7e20a4`, receipt SHA `89eac344f978529aee1b1fe9d68f70895b6e875bbebbb99f980642f206c4eea3`, exit 0 and no input drift. This source-bound compilation/command-diagnostic evidence is reused; no runtime/pin re-audit was performed. Superseded v1 `1459dc6b…` failed on its separate-Ext-world categorical encoding and stays distinct from current v2.

No compilation, probe, lint, test, replay, axiom check, network or Git mutation was performed by this reviewer. All three Scheme images remain unapplied/uncompiled under the current P6 execution hold, and the exact C1 generic still has its own pending elaboration condition. Those conditions remain author/principal-owned. No full continuity, comparison invertibility, enough-injectives result, full-family acceptance or established status is claimed. Existing review history is retained.

