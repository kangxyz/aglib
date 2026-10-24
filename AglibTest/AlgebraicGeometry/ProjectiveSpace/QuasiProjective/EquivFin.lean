/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.EquivFin

/-!
# H-quasi-projective schemes with `n + 1` homogeneous coordinates

The declarations below restate that an H-quasi-projective morphism to `Spec R` has a quasi-compact
immersion into projective space whose coordinates are equivalent to `Fin (n + 1)`, also for an
H-projective morphism and over `Spec A` for a ring `A` in the form taken by the Hilbert schemes of
an immersed scheme, and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.QuasiProjectiveEquivFin

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- **The normalized immersion**, for an H-quasi-projective and for an H-projective morphism. -/
theorem exists_isImmersion (f : X ⟶ Spec R) [IsHQuasiProjective f] (g : X ⟶ Spec R)
    [IsHProjective g] :
    (∃ (ι : Type u) (n : ℕ) (_ : ι ≃ Fin (n + 1)) (i : X ⟶ ProjectiveSpace R ι),
      IsImmersion i ∧ QuasiCompact i ∧ i ≫ ProjectiveSpace.toSpec R ι = f) ∧
      ∃ (ι : Type u) (n : ℕ) (_ : ι ≃ Fin (n + 1)) (i : X ⟶ ProjectiveSpace R ι),
        IsImmersion i ∧ QuasiCompact i ∧ i ≫ ProjectiveSpace.toSpec R ι = g :=
  ⟨IsHQuasiProjective.exists_isImmersion_equivFin f,
    IsHQuasiProjective.exists_isImmersion_equivFin g⟩

/-- **Over `Spec A` for a ring `A`**, in the coordinates `ProjectiveSpace A ι` and
`ProjectiveSpace.toSpec A ι` of the Hilbert schemes of an immersed scheme. -/
theorem exists_isImmersion_of_ring {A : Type u} [CommRing A] (f : X ⟶ Spec (CommRingCat.of A))
    [IsHQuasiProjective f] :
    ∃ (ι : Type u) (n : ℕ) (_ : ι ≃ Fin (n + 1)) (i : X ⟶ ProjectiveSpace A ι),
      IsImmersion i ∧ QuasiCompact i ∧ i ≫ ProjectiveSpace.toSpec A ι = f :=
  IsHQuasiProjective.exists_isImmersion_equivFin f

end AglibTest.QuasiProjectiveEquivFin

/-- info: 'AlgebraicGeometry.IsHQuasiProjective.exists_isImmersion_equivFin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.IsHQuasiProjective.exists_isImmersion_equivFin

/-- info: 'AglibTest.QuasiProjectiveEquivFin.exists_isImmersion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjectiveEquivFin.exists_isImmersion

/-- info: 'AglibTest.QuasiProjectiveEquivFin.exists_isImmersion_of_ring' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.QuasiProjectiveEquivFin.exists_isImmersion_of_ring
