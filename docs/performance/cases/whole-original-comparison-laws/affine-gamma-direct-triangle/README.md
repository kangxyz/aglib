# Apply the original Γ-map equation to the original section value

> Historical source-bound record: names, hashes, checks and limits below refer to
> the stated original executions, not a fresh check of the current sources.

## Scope and retained mathematics

This case concerns `Modules/QuasiCoherent/Affine/TildePullback.lean`, with arbitrary
original `R S T : CommRingCat.{u}`, raw maps `f : R →+* S`, `g : S →+* T`, and
an arbitrary proof of the original Spec triangle. The target is the complete
native tilde/pullback composition law, including its scalar associator, inverse
pullback-composition comparison and actual equality-comparison map. All nine
public lemma/theorem headers were preserved through the final repair. No
flatness, quasicoherence, finiteness or additional square premise was introduced.
The generic component derivation keeps six object and six hom universes independent.

The final repair has three coordinated parts:

1. Move the ONE existing mates proof to a natural-transformation producer accepting
   the original given triangle proof directly. The canonical public natural law
   remains a thin specialization at `Spec.map_comp`. Evaluate that same direct
   proof through the existing generic component backend; do not convert an opaque
   canonical component equation to the arbitrary-proof equation afterward.
2. Move an already-existing general Γ-map pointwise implementation from the tensor
   consumer to the low affine `Sections` owner. Derive its native top-section
   whole-function view from that same pointwise proof. Do not duplicate a section
   backend or import the higher tensor owner into TildePullback.
3. Evaluate that proved whole-function equation with `congrFun`, and let the
   unchanged original goal infer its input in `Eq.trans`. This avoids both the
   failed whole-goal presentation change and unsuccessful lambda-pattern rewrites.

This is not evidence that any one constructor, coercion or proof choice uniquely
caused the earlier failures. Several representations and proof interfaces changed;
there is no controlled matched-speedup claim.

## Native source bridge

The existing private theorem in `Modules/Tensor/AffineSections.lean` was:

```lean
private theorem moduleSpecΓFunctor_map_apply {M N : (Spec R).Modules}
    (f : M ⟶ N) (m : Γ(M, ⊤)) :
    ((moduleSpecΓFunctor (R := R)).map f) m = f.val.app (op ⊤) m := rfl
```

It moved once to `Modules/QuasiCoherent/Affine/Sections.lean`, public with `by rfl`.
Its actual Tensor caller is unchanged. The low owner imports Mathlib's native
`Modules.Tilde`; the Tensor import closure already included it. TildePullback adds
only that lower import. The whole-function consequence is:

```lean
theorem moduleSpecΓFunctor_map_coe {M N : (Spec R).Modules} (k : M ⟶ N) :
    (fun m : Γ(M, ⊤) => ((moduleSpecΓFunctor (R := R)).map k) m) =
      (fun m : Γ(M, ⊤) => (k.app ⊤) m) := by
  funext m
  exact moduleSpecΓFunctor_map_apply k m
```

Native `Scheme.Modules.Hom.app k U` is the forgetful image of
`k.val.app (.op U)`. The underlying function is unchanged. The theorem equates
functions on the original section carriers, not linear maps over different
scalar presentations. Mathlib's Γ functor is the actual module-valued sheaf
forgetful functor followed by top-open evaluation; scalar restriction preserves
underlying functions. No concrete Spec/pushforward object is unfolded in the
consumer to establish this fact.

## Exact final producer calculation

After the original conjugate-equivalence/mates rewrites, the existing `ext M x`
and component `simp only` produce a goal whose outer left side is

```lean
(ModuleCat.Hom.hom
  (moduleSpecΓFunctor.map ((pushforwardCongr h).inv.app M))) originalInnerValue
```

Here `originalInnerValue` is explanatory notation only. Production does not
introduce or restate it: it is the original nested pushforward-composition,
global-sections comparison and restriction-of-scalars application to `x`.
The final source uses:

```lean
refine (congrFun (moduleSpecΓFunctor_map_coe (R := R)
  ((pushforwardCongr h).inv.app M)) _).trans ?_
rw [pushforwardCongr_inv_app_app, eqToHom_op, eqToHom_map]
rfl
```

The original goal determines the placeholder. The producer now proves the
arbitrary-h section calculation itself; it does not assume a compatibility
square or use a canonical-proof transport to bypass it. Existing canonical and
bundled APIs consume this one proof, and the unchanged generic clean component
lemma removes native identity components. Obsolete proof-choice helper code was
removed rather than retained as a parallel backend.

## Earlier component approaches and what their evidence established

The historical canonical natural primitive passed its own normal check at
source `e6844738` (own010, 27s selected leaf). This did not accept later expanded
component owners. The following changes remained unsuccessful at their actual
current source boundaries:

- Concrete component derivations and their outer-let repairs (`c6ba`, `3bfc`)
  encountered ordinary rewrite failures and then named kernel-memory failures.
  Correcting ordinary roots did not itself certify later declarations.
- A variable-category complete natural-law evaluation with twelve independent
  universes (`f6c`) first had a composed-`Functor.obj` carrier mismatch. Adding
  only native `Functor.comp_obj` cleared that emitted ordinary error, while a
  subsequent current locator still reported kernel memory in arbitrary-h rawapp.
- Removing concrete proof-argument `obtain rfl`, giving the complete original
  Eq/Hom carrier, and transporting proof choice over variable natural laws
  (`35b8`, `f486`, `e60d`) did not establish whole-owner acceptance.
- Canonical raw_aux reuse plus a genuine variable-scheme proof-choice equality
  and one variable-morphism cleanup law (`6a4`) still failed at rawapp. The same
  holds for explicit given-h native comparison arguments (`6d919`), original
  R/T constructor elimination (`94e838`), and explicit R/T at the canonical
  raw_aux application (`273362`). No S elimination was justified or applied.

A theorem-binder formation diagnostic (`0fbae`, normal 26.18s, exit0) checked
only the exact proposition as a hypothesis of `True`; it did not check the
actual rawapp proof. Bounded result and proof-input metadata deliberately stopped
before final application/kernel. They reported raw constructor heads, not semantic
inequality or definitional equality. The actual second-premise inspection (`798f`)
opened only the four original type-envelope lets, found matching immediate heads,
and saw unchanged S together with constructor-versus-local-alias R/T. These facts
did not justify an endless endpoint walk or prove that the proof input matched.

## Source-bound phase observations leading to the final repair

Native normal runs used 7000 per frontend, aggregate7168 and one thread, with
actual child argv retained for the runs below. Original package/toolchain settings
were unchanged. Explicitly authorized 6000 check-only locators had no artifact
flags and did not change normal defaults. A guard-only result was not assigned a
kernel/elaboration phase from an earlier source.

| Actual source/run | Retained result and scope |
| --- | --- |
| e60d own063 | Normal aggregate guard107.09s, no declaration phase. Current locator008: sole kernel282,110.56s. |
| 6a4 own068 | Normal aggregate guard92.99s. Current locator009: sole kernel275,110.55s. |
| 6d919 own072 | Normal aggregate guard92.83s. Current locator010: sole kernel275,84.41s. |
| 94e838 own076 | NORMAL native kernel275,151.12s total/147s leaf, no aggregate guard. R/T elimination was insufficient. |
| 273362 own077 | Normal aggregate guard111.60s, no phase. Current locator011: sole kernel275,93.05s. |
| df3db5 own080 | Direct arbitrary-h producer: ordinary whnf timeout at declaration91,72.54s; later unknown-private-constant errors were consequences, not independent diagnoses. |
| d5ca diagnostic008 | Original producer entered; `change` and conjugate injectivity completed; before-section marker reached. No final-section marker/stop.22.92s. |
| aba754 diagnostic009 | Original section `ext` and `simp only` completed. Presentation-only `change` did not complete;30.40s. No proof/kernel acceptance. |
| 46d725 own086 | Deleting that `change` exposed ordinary rewrite157 failure26.22s: goal still had Γ.map, while the native lemma expected `Hom.app ... ⊤`. |
| Sections614b own087 | Actual changed low owner PASS3s selected/6.04s total. |
| Tensorba3a own088 | Actual changed Tensor owner PASS30s selected/63.73s total after only required input refresh. |
| Tildea1eb own089 | First whole-function `rw` pattern failed27.84s: function lambda/`ConcreteCategory.hom` versus actual `ModuleCat.Hom.hom` application. |
| Tildeaedf own092 | Standard local `erw` at that single bridge still failed with the same pattern33.05s. No global transparency change or `.all` rewrite was tried. |
| Tilde1d9e own093 | Goal-directed `congrFun`/`Eq.trans` of the SAME accepted function law: whole owner PASS38s selected/41.99s total, exit0/no guard/group gone. |

The header/comparison pin candidate `627bc` was staged but never promoted or run:
the strict stages had already shown the original header/change and mates proof
completed. It is not a failed native measurement or a repair contributing to the
accepted result. Earlier admission-only probes (including a wrong native accessor)
are likewise not mathematical mismatch evidence.

## Exact accepted sources and validation limits

- `Affine/Sections.lean`:
  `614bce495f35ff8d41dcb5a038866fd86d9f1b581f7226daa89632df40e4a12f`.
- `Modules/Tensor/AffineSections.lean`:
  `ba3a379736b62e4c1006edfd6b0725e40d795af6b051f63578056adf93922431`.
- `Affine/TildePullback.lean`:
  `1d9e56379857346f5c516263f93dea7397a21125a76ac1d1a5f93b74adc8e2db`.

The accepted Tilde check ran on repository HEAD
`1ca5335011920ec972ee4a9ff5da2ea864fda7dd` with the existing pinned toolchain/locks.
The full source was captured in FULL1803 on 2026-11-01 at10:03:00.753147UTC;
its delivery was accepted at10:04:20.315078UTC.
The recovery bundle retains the named own/locator/diagnostic logs, receipts,
source snapshots, strict stage sidecars and exact diffs. The adjacent evidence
index records hashes of the original retained files; these are not invented
compiler receipts. Printed Lake wrapper-input flags are not a substitute for
observed child argv; own093 retains the latter.

Whole Tilde acceptance includes the direct arbitrary-h natural law and all its
raw/bundled component APIs. It is stronger than statement formation or a strict
metadata stop, but does not accept the actual Nonflat caller, coefficient-transfer
factory, fixed-resolution homology comparisons, gluing or arbitrary-field canonical
generation. Those remain their own mathematical/native gates at this milestone.

The reusable method is conditional: when an actual goal retains Γ.map and its
native section rewrite cannot match, expose the existing proved generic map law
at the native section interface. If rewriting a whole-function lambda fails,
evaluate that equality once against the original goal rather than synthesizing
a giant equivalent target. Diagnose actual phase changes before altering more
endpoints, and retain the full history when the repair spans more than one boundary.
