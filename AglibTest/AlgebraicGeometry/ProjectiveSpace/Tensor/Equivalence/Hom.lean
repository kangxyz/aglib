/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence.Hom

/-! Focused consumer of morphisms from a negative twist as sections of the positive twist, with
axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

-- The `Module Γ(X, ⊤)` structure on `M.val.obj (op ⊤)` is found only with `respectTransparency`
-- off, as in the library leaf.
set_option backward.isDefEq.respectTransparency false in
/-- Morphisms `𝒪(-d) ⟶ M` are the global sections of `𝒪(d) ⊗ M`, linearly over `Γ(P, ⊤)`. -/
noncomputable example {R : Type u} [CommRing R] {ι : Type u} (d : ℤ) (M : (ProjectiveSpace R ι).Modules) :
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) (RingHom.id _)
    letI : Module Γ(ProjectiveSpace R ι, ⊤) (((moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι d)).obj M).val.obj (op ⊤)) := Module.compHom _ (RingHom.id _)
    (twistingSheaf R ι (-d) ⟶ M) ≃ₗ[Γ(ProjectiveSpace R ι, ⊤)]
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj M).val.obj
        (op ⊤) :=
  negativeTwistHomLinearEquivSections (RingHom.id _) d M

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensorNegIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensorNegIso

/--
info: 'AlgebraicGeometry.ProjectiveSpace.negativeTwistHomLinearEquivSections' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.negativeTwistHomLinearEquivSections
