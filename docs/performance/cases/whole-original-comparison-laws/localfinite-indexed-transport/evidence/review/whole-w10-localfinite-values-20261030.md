# Ordinary review of the v29 finite-source comparison

**The mathematical derivation and native source correspondence are supported for the fixed v29 pair, and both exact modules now have matching ordinary CPP success.** No additional mathematical premise or correspondence defect was found in the assigned closure. This is an independent ordinary review, with no established-status or writing-acceptance decision and no whole-W10 closure claim.

The reviewer did not author this construction or supply an incorporated repair. Only these two review files are written. No Lean, test, lint, probe, network, replay or client check was run.

## Fixed basis

N is `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/aglib`, at HEAD `3ab570353d8ccfb0db62b01300f7be9a79ec44a8` with the identified dirty sources. Entry HEAD is `3467423400c765167730d4372704650a52ab3a95`. Live and immutable candidate bytes matched before delivery.

| File relative to N | SHA-256 |
|---|---|
| `Aglib/CategoryTheory/Abelian/Ext/OriginalComparisonValues.lean` | `e1d0a92737405aec68ed643078b79eaf9bcbbab736d82ea9aa429caed14a133d` |
| `Aglib/AlgebraicGeometry/EtaleCohomology/Fields/SeparableExtension/FiniteConstants/LocalFiniteComparison.lean` | `0997517ed89eba60a57505a6665d1fc722afec046cf6afaa726ff8e4462d6988` |
| `Aglib/CategoryTheory/Abelian/Ext/OriginalComparison.lean` (unchanged) | `b4326fdbaf28b225738ddb9f5dedc254db39b3f641c440cab60b98c6f05a311e` |

The current packet is `migration/implementation/whole-w10-remaining/localfinite-indexed-transport-v29`: `READY.json` is `dfc700b916b6c1b177f02a07b1b039525637adc1d4a4db220aa03544c08da32a`; `LIVE_READY.json` is `b35957397fe14f07665cbb66ac4e73aa8861a3808c6c84a549bb2644b1538077`. The candidate was initially R-only and became LIVE during review with identical bytes. Live and immutable candidate/before identities matched before report update.

The v26 five-declaration comparison construction and context remain byte-identical. V29 removes the sole-use v28 ordinary transport helper and adds the indexed adjunction wrapper. Native changes only its source-equation/final-factory application; the three public headers, private original-family identity and complete corollary suffix are unchanged. The removed helper's earlier mathematical verdict remains historical and is no longer current dependency coverage.

This continues the assigned v26/v28 review. Prior v28 report hashes were Markdown `331bfa8ed40b3f056b8298e16583cfaa58c5fc8039d43008f67c42ab312c7ec5`, JSON `f9b3a46e851de70e79483c12ac437200a91beeb26231ef65709c5a4ef4c6709c`. No previous mathematical conclusion is withdrawn. Earlier pending execution states are replaced below by their actual same-source outcomes; old results are not attributed to the v29 pair.

## Construction and original-map correspondence

Write `E(M,n) = originalExtSourceComparison adj e M n` and similarly `E'(M,n)` for `adj',e',H(M)`. Each is constructed from the **same** exact adjunction and inverse source-isomorphism transport. The pinned mathlib `Adjunction.extEquiv` uses the actual exact-functor map, unit and counit, with independent `HasExt` universes; it supplies no arbitrary endpoint equivalence.

The new definition is the whole additive family

```text
K(M,n) = E'(M,n) ∘ (β_M)_* ∘ pG(R(M),n) ∘ E(M,n)⁻¹.
```

Here `(β_M)_*` is literally postcomposition by `Ext.mk₀ (β.app M)`. The ordinary mate-counit equation, together with both source-factorization laws, gives the existing `originalExtSourceComparison_mate_square` through `extCoefficientTransfer_square`. Substituting `E(M,n)⁻¹(a)` and using its inverse law proves `K(M,n)(a)=pH(M,n)(a)`. Additive-hom and dependent-function extensionality produce **whole family equality** `K=pH`. Thus the cohomology square is derived; the new inputs are the defining identities of the original maps and mate.

The selected coefficient transport is bijective because `extFunctorObj` sends an isomorphism to exactly that postcomposition map. Composing it with `E⁻¹`, the assumed selected base-map bijection, and `E'` proves bijectivity of `K(M,n)`, hence of the supplied `pH(M,n)`. Invertibility of all exchange components is unnecessary.

The native correspondence is exact:

| Generic datum | Native datum |
|---|---|
| `C₀,C₁,C₂,C₃` / Ext worlds | Sheaves on `S,X,S',X'` / `eS,eX,eS',eX'` |
| `L,R,adj` and primed data | Original inverse/direct images and adjunctions of `f,f'` |
| `G,H` | Original inverse images of `g,g'` |
| `Uᵢ,e,e',sG,sH` | Original constant lifted-integer sheaves and the stated constant-comparison components/inverses |
| `L₀,c,d` | `inverseImage (f' ≫ g)`, `inverseImageComp g f'`, and transport along `h.w.symm` followed by `inverseImageComp f g'` |
| `β,pG,pH` | Literal `baseChangeMap` and whole original `cohomologyPullback g`, `cohomologyPullback g'` families |

Both pullback-family identities are definitional (`Pullback.lean:49`). `hs` remains `inverseImageComp_constant_inv`. The native caller supplies the inferred `hSourceComp := inverseImageComp_constant_inv f g' A`. `hMate` still follows from `baseChangeMap_eq_nativeMate` and `inverseImageSquareIso_eq_comp`. No cohomology equation is assumed.

The new `originalExtSourceComparison_bijective_of_transport_values` wrapper takes an indexed functor family `K : I → C₀ ⥤ C₃`, equal indices `h : i=j`, a source-arrow family `s(k) : U₃ ⟶ (K k).obj U₀`, and original comparisons `c₀ : K i ≅ G ⋙ L'`, `d₁ : K j ≅ L ⋙ H`. Its source premises are the independent original laws

```text
hleft:  s i ≫ c₀.hom.app U₀ = e'.inv ≫ L'.map sG
hright: s j ≫ d₁.hom.app U₀ = sH ≫ H.map e.inv.
```

Equality induction on `h`, followed by `eqToIso_refl` and `Iso.refl_trans`, derives internally

```text
ht: s i ≫ (eqToIso (congrArg K h) ≪≫ d₁).hom.app U₀
      = sH ≫ H.map e.inv.
```

It immediately applies the unchanged mate-values theorem with `L₀=K i`, `c=c₀`, `d=eqToIso (congrArg K h) ≪≫ d₁`, and `s₀=s i`. Exactness is required only for the selected `K i`, together with the existing exact-functor assumptions; there is no all-index exactness hypothesis. The same original adjunction/source comparisons, literal exchange, original map-definition equations and selected bijectivity inputs then give bijectivity of the supplied `pH(M,n)`. The transported source equation is derived inside this generic construction and is not a new parameter.

Native substitution is `I=(X' ⟶ S)`, `i=f' ≫ g`, `j=g' ≫ f`, `h=h.w.symm`, `K=inverseImage`, and `s(k)=((inverseImageConstantIso k).app A).inv`. The comparisons are `inverseImageComp g f'` and `inverseImageComp f g'`; the source inputs are unchanged `hs` and the inferred original `hSourceComp`. The new mate expression is exactly `c.symm ≪≫ d`: `≪≫` is right-associative, and `d` is the unchanged equality transport followed by `inverseImageComp f g'`. Thus `hMate` is the same existing witness. The final `pH` remains the literal original cohomology-pullback family. The index universe introduces no identification of the four Ext worlds or new geometric model.

The Cartesian square and finite `f` supply finite `f'`. `Finite/HigherVanishing.lean:30` supplies finite-colimit preservation of both original direct images; `DirectImage.lean:48` and the adjunction supply their additive/finite-limit structure. `H1/Pullback.lean:45` supplies exact additive inverse images. `Finite/ExactImageComparison/OrdinaryBaseChange.lean:63` supplies **the literal selected** `IsIso ((baseChangeMap ...).app F)`. These providers have precisely the original geometry and arbitrary-coefficient scope. Their applicability is checked here; their accepted geometric proof towers are not reopened.

The three public headers and both later corollary bodies are byte-preserved against native `9f80c35b47e879a9a26fd0b60182abfa9af221473456a8d8b809a28e3138065a`. The subsequent `HasExt.standard` scope is unchanged. There is no new Ext-world identification, reference category, arbitrary comparison, torsion/dimension hypothesis on the first theorem, or restriction on its natural degree.

## Result-specific verdicts

In these identifiers, `G` denotes `Aglib/CategoryTheory/Abelian/Ext/OriginalComparisonValues.lean`; `L` denotes `Aglib/AlgebraicGeometry/EtaleCohomology/Fields/SeparableExtension/FiniteConstants/LocalFiniteComparison.lean`. The JSON records each full `ID#label`.

- `G#originalExtSourceComparisonConjugate`: **supported construction** of the additive family `K` displayed above from exact adjunctions and source isomorphisms.
- `G#originalExtSourceComparisonConjugate_apply`: **supported** exact evaluation formula `K(M,n)(a)=E'((pG(R(M),n)(E⁻¹(a)))·mk₀(β_M))` in every degree.
- `G#originalExtSourceComparisonConjugate_bijective`: **supported** bijectivity of `K(M,n)` assuming only the selected `β_M` is invertible and `pG(R(M),n)` is bijective, under the definition's exact-adjunction hypotheses.
- `G#originalExtSourceComparisonConjugate_eq`: **supported** whole equality `K=pH`, under exact additive `G,H,L₀`, the original comparisons `c,d`, both displayed source laws, the original mate identity and both whole map-definition identities.
- `G#originalExtSourceComparison_bijective_of_mate_values`: **supported** bijectivity of `pH(M,n)` under those same identities, selected exchange invertibility and selected base-map bijectivity.
- `G#originalExtSourceComparison_bijective_of_transport_values`: **supported new v29 derivation/native application; matching ordinary CPP passed**. With the indexed functors, original source family, equality and two original source laws displayed above, the original transported mate identity, whole `pG/pH` definitions, selected `β_M` invertibility and base-map bijectivity imply `Bijective(pH(M,n))`. The transported source equation is internally proved by equality induction and immediately consumed by the unchanged factory.
- `L#cohomologyPullback_originalFamily`: **supported** definitional equality of the whole original pullback family with exact inverse-image Ext pullback through the canonical constant-integer inverse, retaining its two independent Ext worlds.
- `L#cohomologyPullback_source_bijective_of_finiteDirectImage`: **supported mathematics/source correspondence; matching ordinary CPP passed**. For the original four schemes and independent Ext worlds, finite `f`, the Cartesian square, arbitrary coefficient `F` and every `q : ℕ`, bijectivity of the original `g`-pullback of `f_*F` implies bijectivity of the original `g'`-pullback of `F`.
- `L#finite_projectiveLine_residuePullback_bijective_of_killed_of_isNoetherian`: **supported affected use; unchanged body; matching ordinary CPP passed**. Over a Noetherian Henselian local commutative ring with separably closed residue field, for finite `f:Y→P¹_R`, `n≠0`, `n • 𝟙 F=0` and every `q`, the original pullback of `F` along `pullback.fst (f ≫ structureMap R) (residueSpecMap R)` is bijective in the original standard Ext worlds. Additivity transports annihilation to `f_*F`; the unchanged projective-line provider supplies the base comparison.
- `L#finite_projectiveLine_constantRestriction_bijective_of_isNoetherian`: **supported affected use; unchanged body; matching ordinary CPP passed**. Under that same base and finite-cover geometry, for every finite additive commutative group `A` and every `q`, the literal `constantRestriction A` along that closed-fibre projection is bijective in the same standard Ext worlds. The positive group cardinal kills its constant sheaf, and `ConstantRestriction.lean:36–47` identifies the resulting original pullback followed by the original coefficient isomorphism with this literal restriction map.

## Evidence and scope

The matching local mathlib source remains revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. The unchanged exact-adjunction Ext, coefficient functor and mate-counit inputs were inspected in the initial review. This continuation additionally checked `CategoryTheory/Iso.lean:142` for the exact composition notation. The JSON records full source identities, conditions, ten result-specific current verdicts and the retired v28 declaration's historical verdict.

The actual execution evidence is version-specific:

- The original `9f80…` native failure remains its historical result. The separate `7f2c…` formation success places the original full cohomology proposition only in `(_h : P) : True`; it proves neither `P` nor formation of every later ordinary source equality.
- V26 `remote-2f7f18787712437fb879d329b7835330`, SOURCE `0f46750592aec8cc2718833f0dfe763e6cad34db10a11d5fe86d483a03d278f6`: closed, drift-free mixed exit 1; generic `aa3d…` passed and native `f656…` failed. Its five unchanged generic declarations retain compatible coverage.
- V28 `remote-4e0c2743acea48b6ab6c56bb886f5d9f`, SOURCE `97107a0b67721e67791420a016ca36ebc5ec9df36a5f3efc4d35a356ad56ec2c`: closed, drift-free mixed exit 1; generic `b62f…` passed and native `655b…` failed. The source-bound summary `CPP-4e0c2743-LocalFinite-v28-final.json` has SHA-256 `b3d4e668260a81500184c0a5638682e89b6d750adeb4b090fae355ccd2281f9d`. Selected raw receipt fields confirm two invocations, one success and one failure. This supersedes the previous v28 pending state; it is not a v29 result.
- The corrected `d5e3…` old-source diagnostic separately records whole-family kernel success, standalone sourceSecond/`ht` kernel timeout and full-proof kernel timeout. Its recorded full log remains at its owner; no full-log reread or new execution was performed here.
- The normal standalone sourceSecond runs `remote-f94cbbd112f441ee862f57fa10e240a2` / scratch `fe59264a1712d3b1876e221314b73fdd604d3578565561c0951963a13ed82155` and `remote-e2d8b8ce14a3479eacc998b0f5835fe8` / scratch `86fe6ef137da28646e37604b649306d22e78d0cb540a45192bfd7345e6b7674d` share SOURCE `a6900933b6f95bed43897ed4902dc03cefad54333bf4b53801386ef5f77d396d` and both fail in the kernel. The latter bounded RESULT is `localfinite-literal-transport-normal-v1/RESULT.json`, SHA-256 `0ef1c3faca0f033180ce655f835f472d3ae52d1effe6b153f11b31f8472da28b`. The inspected scratch source is an ordinary Scheme source equation with no `HasExt`, coefficient `F` or cohomological degree. These failures do **not** separate equality type formation from proof checking, identify a concrete expected/inferred conversion pair, or establish a unique data/model cause.

The fixed v29 pair now has **actual matching ordinary CPP success** in `remote-22047e1ff0a3472cb67017d7b5df75fd`, SOURCE `3bac8faa52cdef9b8a34cc9a7fea0a1558bf6e8df9fcd59edf15112cd9c1fd1f`. The canonical receipt reports closed exit 0, two compiler invocations/two successes, no failures, no unfinished events and no input drift. It uses Lean 4.34.1 and the standard profile of eight jobs, four threads, 12,800 MiB per compiler and 65,536 MiB RSS ceiling.

| Exact module | Actual compiler outcome |
|---|---|
| `OriginalComparisonValues.lean`, `e1d0a927…` | Compiler 303326, exit 0, 3.648185 s |
| `LocalFiniteComparison.lean`, `0997517e…` | Compiler 303336, exit 0, 49.771698 s |

The source-bound result is `migration/implementation/whole-w10-remaining/CPP-22047e1f-LocalFinite-v29-final.json`, SHA-256 `8b8f79cf1bbbb55ab9139184fd33110b3ada05df35e80af5228fd11f94054a26`. The independently inspected canonical files are under `foundations/lane-a/remote-runs/remote-22047e1ff0a3472cb67017d7b5df75fd/`: `receipt.json` SHA-256 `6931db7ca1c9f07128936e0a395d55b64bfda135bec5cf3d7398316250a8d68e`, `compiler-events.jsonl` SHA-256 `3d159c1fb83410d88f23e32fb937c3563e666c1384b8acdc18ed7ad3ee3eb33e`, and `build.log` SHA-256 `80984f252e4d537fa0530dc2b67dbf44795fe7ae92153a0387baedb5051939ec`. Native/configuration input hashes and the current reviewed pair/providers matched. The source owner supplies the consumed exact-vector/changed-lower binding; the full SOURCE descriptor is archival follow-up, not a new review or execution gate.

This evidence update supersedes only the report's prior v29 CPP-pending state (previous Markdown SHA-256 `7ac09cc3c0fc1f54500149cab511877ebdab96d1901417b8fe725fd08d78d5a1`, JSON `aff1f6ea5fd137acd92dadcf8f106e7e871cce498abbc4cd9972302afeac6400`). The candidate and mathematical verdict are unchanged. **No mathematical/source-correspondence or ordinary-CPP gap remains in this fixed assigned LocalFinite closure under its accepted providers.** No reviewer run, new review cycle, standalone gate, controlled speedup claim or blanket downstream result is added. NativeLine is not covered by these two passes.

Unchanged V24/pure-core coverage remains on its own basis. Germ, Section, Relative, Primitive, the other module outcomes and prior unrelated reports are neither reopened nor reissued. Only this assigned review pair is updated, with explicit source/version reconciliation. No status decision follows from this ordinary verdict.

Reproduce source identities with `shasum -a 256` on the named files and the bounded source delta with `diff -u` on the packet's `before/` and `source/` files. The completed owning CPP is reused without another run.
