/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence
public import Aglib.AlgebraicGeometry.Modules.Tensor.Linear
public import Aglib.AlgebraicGeometry.Modules.Linear

/-!
# Morphisms from a negative twist as sections of the positive twist

On `P = ProjectiveSpace R ι`, opposite twists tensor to the structure module
(`twistingTensorNegIso`), and tensoring with `𝒪(d)` identifies morphisms `𝒪(-d) ⟶ M` with
morphisms `𝒪 ⟶ 𝒪(d) ⊗ M`, hence with the global sections of `𝒪(d) ⊗ M`, linearly over any
specified structural ring map `α : A →+* Γ(P, ⊤)` (`negativeTwistHomLinearEquivSections`). This
is a different map from `twistingGlobalSectionsHomLinearEquivOfHom`, which identifies morphisms
between twists with sections by multiplication. No finiteness or quasicoherence is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R] {ι : Type u}

/-- Opposite twists tensor to the structure module, through the original multiplication and the
zero-twist unit map. -/
def twistingTensorNegIso (d : ℤ) :
    (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj
        (twistingSheaf R ι (-d)) ≅ SheafOfModules.unit (ProjectiveSpace R ι).ringCatSheaf :=
  twistingTensorIso R ι d (-d) ≪≫
    eqToIso (congrArg (twistingSheaf R ι) (add_neg_cancel d)) ≪≫ twistingZeroIso R ι

section Linear

variable {A : Type v} [CommRing A] (α : A →+* Γ(ProjectiveSpace R ι, ⊤))

/-- **Morphisms from a negative twist are global sections of the positive twist**, linearly over
any specified structural ring map:
`Hom(O(-d), M) ≅ Hom(O(d) ⊗ O(-d), O(d) ⊗ M) ≅ Hom(𝒪, O(d) ⊗ M) ≅ Γ(P, O(d) ⊗ M)`, through the
tensor equivalence `twistingTensorEquivalence`. -/
def negativeTwistHomLinearEquivSections (d : ℤ) (M : (ProjectiveSpace R ι).Modules) :
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    letI : Module A (((moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι d)).obj M).val.obj (op ⊤)) := Module.compHom _ α
    (twistingSheaf R ι (-d) ⟶ M) ≃ₗ[A]
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj M).val.obj
        (op ⊤) := by
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  exact (LinearEquiv.ofBijective
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).mapLinearMap A)
      ⟨(moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map_injective,
        (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map_surjective⟩).trans
    ((Linear.homCongr A (twistingTensorNegIso d) (Iso.refl _)).trans
      (unitHomGlobalSectionsLinearEquivOfHom _ α _))

end Linear

end AlgebraicGeometry.ProjectiveSpace
