/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.HilbertScheme.Immersed.QuasiProjective

/-! Focused consumer of the quasi-projectivity of the Hilbert scheme of a locally closed subscheme
`Y ⊆ P^n_A` (Nitsure, arXiv:math/0504590v1, Thm 6.1, p. 28), with an axiom guard. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open scoped Polynomial

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (ι : Type u) (n : ℕ)
  (e : ι ≃ Fin (n + 1)) (Φ : ℚ[X]) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))
  {Y : Scheme.{u}} (i : Y ⟶ ProjectiveSpace A ι) [IsImmersion i]

/-- **The Hilbert scheme of `Y` is H-quasi-projective over `Spec A`**, hence separated,
quasi-compact and locally of finite type over `Spec A`. -/
example :
    IsHQuasiProjective (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom ∧
      IsSeparated (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom ∧
        QuasiCompact (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom ∧
          LocallyOfFiniteType (immersedHilbertSchemeOver ι n e A Φ r hr φ i).obj.hom :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/--
info: 'AlgebraicGeometry.ProjectiveSpace.isHQuasiProjective_immersedHilbertSchemeOver_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.isHQuasiProjective_immersedHilbertSchemeOver_hom
