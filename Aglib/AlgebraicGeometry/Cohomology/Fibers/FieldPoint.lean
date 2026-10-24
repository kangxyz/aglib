/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Fibers.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.FieldExtension

/-!
# Cohomology dimensions over field-valued points

For a field `K` and a scheme `b : Y ⟶ Spec K`, `moduleCohomologyDimension b M q` is the dimension
over `K` of the original cohomology `H^q(Y, M)`, for the structural `K`-action through `b`, and
`moduleEulerChar b M` is the alternating sum of these dimensions. They are the invariants of the
base change `X ×_S Spec K` of a morphism `p : X ⟶ S` along a field point `Spec K ⟶ S`:

* invariance under isomorphism of modules (`moduleCohomologyDimension_congr`) and transport along
  isomorphisms over `Spec K` (`moduleCohomologyDimension_eq_of_isIso`, from
  `finrank_moduleCohomology_eq_of_isIso`);
* invariance under field extension for qcqs `b` and quasicoherent `M`
  (`moduleCohomologyDimension_fieldBaseChange`, from `moduleCohomology_finrank_fieldBaseChange`:
  flat base change over a field, Stacks, Tag 02KH; Hartshorne, Prop. III.9.3, is the Noetherian
  separated finite-type case);
* the point fibre of `X ×_S T ⟶ T` at `t` is the base change along `Spec κ(t) ⟶ T ⟶ S`
  (`modulePointFiberCohomologyDimension_eq_pullbackMap`), through the pasting isomorphism
  `(X ×_S T) ×_T Spec κ(t) ≅ X ×_S Spec κ(t)`; the pullback of the coefficient is taken along
  `residueFieldBaseChange p s t : X ×_S Spec κ(t) ⟶ X ×_S T`.

No properness, Noetherian, flatness or finiteness hypothesis enters except where stated.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

section Dimension

variable {K : Type u} [Field K] {Y : Scheme.{u}}

/-- The dimension over a field `K` of the original cohomology `H^q(Y, M)`, for the structural
`K`-action through `b : Y ⟶ Spec K`. -/
def moduleCohomologyDimension (b : Y ⟶ Spec (.of K)) (M : Y.Modules) (q : ℕ) : ℕ :=
  letI := moduleCohomologyModuleOfHom Y (b.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) M q
  Module.finrank K (Sheaf.H.{u + 1} (moduleAddSheaf Y M) q)

/-- The Euler characteristic `Σ (-1)^q h^q(Y, M)` over a field `K`. Native `finsum` is zero if
its support is infinite. -/
def moduleEulerChar (b : Y ⟶ Spec (.of K)) (M : Y.Modules) : ℤ :=
  ∑ᶠ q : ℕ, (-1 : ℤ) ^ q * (moduleCohomologyDimension b M q : ℤ)

/-- Isomorphic modules have the same cohomology dimensions. -/
theorem moduleCohomologyDimension_congr (b : Y ⟶ Spec (.of K)) {M N : Y.Modules} (e : M ≅ N)
    (q : ℕ) : moduleCohomologyDimension b M q = moduleCohomologyDimension b N q :=
  ((moduleCohomologyFunctorOfHom Y (b.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    q).mapIso e).toLinearEquiv.finrank_eq

/-- Isomorphic modules have the same Euler characteristic. -/
theorem moduleEulerChar_congr (b : Y ⟶ Spec (.of K)) {M N : Y.Modules} (e : M ≅ N) :
    moduleEulerChar b M = moduleEulerChar b N := by
  simp only [moduleEulerChar, moduleCohomologyDimension_congr b e]

/-- Cohomology dimensions transport along an isomorphism `e : P ⟶ Y` over `Spec K`, for a module
`N` on `P` isomorphic to the pullback of `M`. -/
theorem moduleCohomologyDimension_eq_of_isIso {P : Scheme.{u}} (e : P ⟶ Y) [IsIso e]
    (b : Y ⟶ Spec (.of K)) (t : P ⟶ Spec (.of K)) (w : e ≫ b = t) (M : Y.Modules)
    {N : P.Modules} (C : (Scheme.Modules.pullback e).obj M ≅ N) (q : ℕ) :
    moduleCohomologyDimension b M q = moduleCohomologyDimension t N q :=
  finrank_moduleCohomology_eq_of_isIso e b t w M C q

/-- **Field extension.** For `b : Y ⟶ Spec K` quasi-compact and quasi-separated, a field map
`σ : K →+* K'` and a quasicoherent `M`, the dimension of `H^q(Y ×_K Spec K', M_{K'})` over `K'`
is that of `H^q(Y, M)` over `K` (flat base change over a field). -/
theorem moduleCohomologyDimension_fieldBaseChange (b : Y ⟶ Spec (.of K)) [QuasiCompact b]
    [QuasiSeparated b] {K' : Type u} [Field K'] (σ : K →+* K') (M : Y.Modules)
    [M.IsQuasicoherent] (q : ℕ) :
    moduleCohomologyDimension (pullback.snd b (Spec.map (CommRingCat.ofHom σ)))
        ((Scheme.Modules.pullback (pullback.fst b (Spec.map (CommRingCat.ofHom σ)))).obj M) q =
      moduleCohomologyDimension b M q :=
  moduleCohomology_finrank_fieldBaseChange b σ M q

/-- The point-fibre dimension is `moduleCohomologyDimension` on the native fibre. -/
theorem modulePointFiberCohomologyDimension_eq_moduleCohomologyDimension {X Z : Scheme.{u}}
    (f : X ⟶ Z) (M : X.Modules) (q : ℕ) (z : Z) :
    modulePointFiberCohomologyDimension f M q z =
      moduleCohomologyDimension (K := Z.residueField z) (f.fiberToSpecResidueField z)
        ((Scheme.Modules.pullback (f.fiberι z)).obj M) q :=
  rfl

/-- The point-fibre Euler characteristic is `moduleEulerChar` on the native fibre. -/
theorem modulePointFiberEulerChar_eq_moduleEulerChar {X Z : Scheme.{u}}
    (f : X ⟶ Z) (M : X.Modules) (z : Z) :
    modulePointFiberEulerChar f M z =
      moduleEulerChar (K := Z.residueField z) (f.fiberToSpecResidueField z)
        ((Scheme.Modules.pullback (f.fiberι z)).obj M) :=
  rfl

/-- Point-fibre dimensions of isomorphic modules agree. -/
theorem modulePointFiberCohomologyDimension_congr {X Z : Scheme.{u}} (p : X ⟶ Z)
    {M N : X.Modules} (e : M ≅ N) (q : ℕ) (z : Z) :
    modulePointFiberCohomologyDimension p M q z = modulePointFiberCohomologyDimension p N q z :=
  moduleCohomologyDimension_congr _ ((Scheme.Modules.pullback _).mapIso e) q

/-- Point-fibre Euler characteristics of isomorphic modules agree. -/
theorem modulePointFiberEulerChar_congr {X Z : Scheme.{u}} (p : X ⟶ Z)
    {M N : X.Modules} (e : M ≅ N) (z : Z) :
    modulePointFiberEulerChar p M z = modulePointFiberEulerChar p N z :=
  moduleEulerChar_congr _ ((Scheme.Modules.pullback _).mapIso e)

end Dimension

section PullbackPasting

variable {X S T : Scheme.{u}} (p : X ⟶ S) (s : T ⟶ S)

/-- The pasting isomorphism `(X ×_S T) ×_T W ≅ X ×_S W` followed by the base-change map
`X ×_S W ⟶ X ×_S T` is the first projection. -/
@[reassoc (attr := simp)]
theorem pullbackLeftPullbackSndIso_hom_pullbackMap {W : Scheme.{u}} (x : W ⟶ T) :
    (pullbackLeftPullbackSndIso p s x).hom ≫
        pullback.map p (x ≫ s) p s (𝟙 X) x (𝟙 S) (by simp) (by simp) =
      pullback.fst (pullback.snd p s) x := by
  apply pullback.hom_ext
  · simp
  · simp [pullback.condition]

/-- Dimensions on `(X ×_S T) ×_T Spec K` and on `X ×_S Spec K` agree, for the pullbacks of a
module on `X ×_S T` along the two canonical maps. -/
theorem moduleCohomologyDimension_pullback_snd_pullback_snd {K : Type u} [Field K]
    (x : Spec (.of K) ⟶ T) (M : (pullback p s).Modules) (q : ℕ) :
    moduleCohomologyDimension (pullback.snd (pullback.snd p s) x)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd p s) x)).obj M) q =
      moduleCohomologyDimension (pullback.snd p (x ≫ s))
        ((Scheme.Modules.pullback
          (pullback.map p (x ≫ s) p s (𝟙 X) x (𝟙 S) (by simp) (by simp))).obj M) q := by
  symm
  refine moduleCohomologyDimension_eq_of_isIso (pullbackLeftPullbackSndIso p s x).hom _ _
    (pullbackLeftPullbackSndIso_hom_snd p s x) _ ?_ q
  exact (Scheme.Modules.pullbackComp _ _).app M ≪≫
    (Scheme.Modules.pullbackCongr (pullbackLeftPullbackSndIso_hom_pullbackMap p s x)).app M

/-- The base-change map `X ×_S Spec κ(t) ⟶ X ×_S T` at a point `t ∈ T`. -/
abbrev residueFieldBaseChange (t : T) :
    pullback p (T.fromSpecResidueField t ≫ s) ⟶ pullback p s :=
  pullback.map p (T.fromSpecResidueField t ≫ s) p s (𝟙 X) (T.fromSpecResidueField t) (𝟙 S)
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem residueFieldBaseChange_fst (t : T) :
    residueFieldBaseChange p s t ≫ pullback.fst p s =
      pullback.fst p (T.fromSpecResidueField t ≫ s) := by
  simp [residueFieldBaseChange]

/-- **Point fibres as residue-field base changes.** The point-fibre dimension of a module `M`
on `X ×_S T` at `t` is the dimension on `X ×_S Spec κ(t)` of the pullback of `M`. -/
theorem modulePointFiberCohomologyDimension_eq_pullbackMap (M : (pullback p s).Modules) (q : ℕ)
    (t : T) :
    modulePointFiberCohomologyDimension (pullback.snd p s) M q t =
      moduleCohomologyDimension (K := T.residueField t)
        (pullback.snd p (T.fromSpecResidueField t ≫ s))
        ((Scheme.Modules.pullback (residueFieldBaseChange p s t)).obj M) q :=
  moduleCohomologyDimension_pullback_snd_pullback_snd p s (K := T.residueField t)
    (T.fromSpecResidueField t) M q

/-- **Point fibres as residue-field base changes**, for Euler characteristics. -/
theorem modulePointFiberEulerChar_eq_pullbackMap (M : (pullback p s).Modules) (t : T) :
    modulePointFiberEulerChar (pullback.snd p s) M t =
      moduleEulerChar (K := T.residueField t) (pullback.snd p (T.fromSpecResidueField t ≫ s))
        ((Scheme.Modules.pullback (residueFieldBaseChange p s t)).obj M) := by
  unfold modulePointFiberEulerChar moduleEulerChar
  congr 1
  funext q
  rw [modulePointFiberCohomologyDimension_eq_pullbackMap]

end PullbackPasting

end AlgebraicGeometry.Scheme.Cohomology
