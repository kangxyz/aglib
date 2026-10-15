/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Hom.Sections
public import Aglib.AlgebraicGeometry.Modules.Linear

/-!
# Structural linearity of the original twist Hom comparison

For any specified structural ring map into global functions, the actual multiplication
comparison from original global sections to actual twist morphisms is linear. The section
action is native scalar restriction and the morphism action is the original category center.
No cohomology transport or replacement action is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)
  {A : Type v} [CommRing A] (α : A →+* Γ(ProjectiveSpace R ι, ⊤))

/-- Original global sections and actual twist morphisms are linearly equivalent over any
specified structural ring, with native scalar restriction and the native category action. -/
def twistingGlobalSectionsHomLinearEquivOfHom (a b : ℤ) :
    letI := Module.compHom Γ(twistingSheaf R ι a, ⊤) α
    letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
    Γ(twistingSheaf R ι a, ⊤) ≃ₗ[A]
      (twistingSheaf R ι b ⟶ twistingSheaf R ι (a + b)) := by
  letI := Module.compHom Γ(twistingSheaf R ι a, ⊤) α
  letI := moduleCategoryLinearOfHom (ProjectiveSpace R ι) α
  refine {
    __ := twistingGlobalSectionsHomAddEquiv R ι a b
    map_smul' := fun r s => ?_ }
  apply hom_ext_of_coordinateSubopens R ι
  intro i V hi t
  change (twistingMultiplyGlobal R ι a b (α r • s)).val.app (op V) t =
    (r • twistingMultiplyGlobal R ι a b s).val.app (op V) t
  rw [moduleCategoryLinearOfHom_smul_app]
  change twistingSectionMul R ι a b V
      ((twistingSheaf R ι a).val.map (homOfLE le_top).op (α r • s)) t =
    (ProjectiveSpace R ι).presheaf.map (homOfLE le_top).op (α r) •
      twistingSectionMul R ι a b V
        ((twistingSheaf R ι a).val.map (homOfLE le_top).op s) t
  rw [(twistingSheaf R ι a).val.map_smul]
  exact LinearMap.congr_fun ((twistingSectionMulLinear R ι a b V).map_smul _ _) t

/-- Structural linear enrichment retains the same original multiplication map. -/
theorem twistingGlobalSectionsHomLinearEquivOfHom_apply (a b : ℤ)
    (s : Γ(twistingSheaf R ι a, ⊤)) :
    twistingGlobalSectionsHomLinearEquivOfHom R ι α a b s =
      twistingMultiplyGlobal R ι a b s := rfl

end AlgebraicGeometry.ProjectiveSpace
