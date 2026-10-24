/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Coproduct.QuasiProjective

/-! Focused consumer of the H-quasi-projectivity of the finite disjoint union of Hilbert schemes of
a locally closed subscheme of `P^n_A`, for a finite set of polynomials given as a `Finset`, with
axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) (A : Type u) [CommRing A]
  [IsNoetherianRing A] (F : Finset ℚ[X]) (r : ↥(F : Set ℚ[X]) → ℕ)
  (hr : ∀ Φ : ↥(F : Set ℚ[X]), hilbertRegularityBound n Φ ≤ r Φ)
  {J : ↥(F : Set ℚ[X]) → Type u}
  (φ : ∀ Φ : ↥(F : Set ℚ[X]),
    SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) (J Φ) ⟶
      twistingSheaf A ι (r Φ : ℤ))
  {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i]

/-- **`H_F` is H-quasi-projective over `Spec A`** for a finite set `F` of polynomials; in particular
it is Noetherian, separated and of finite type over `Spec A`. -/
example :
    IsHQuasiProjective (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom ∧
      IsNoetherian (sigmaImmersedHilbertScheme ι n e A r hr φ i) ∧
      IsSeparated (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom :=
  ⟨inferInstance,
    IsHQuasiProjective.isNoetherian (sigmaImmersedHilbertSchemeOver ι n e A r hr φ i).obj.hom,
    inferInstance⟩

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHQuasiProjective_sigmaImmersedHilbertSchemeOver_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.ProjectiveSpace.isHQuasiProjective_sigmaImmersedHilbertSchemeOver_hom

/--
info: 'AlgebraicGeometry.Scheme.LocallyNoetherianOver.isHQuasiProjective_sigma_obj_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.LocallyNoetherianOver.isHQuasiProjective_sigma_obj_hom
