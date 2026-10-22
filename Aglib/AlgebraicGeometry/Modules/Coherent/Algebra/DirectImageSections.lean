/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.DirectImage
public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.Sections

/-!
# Original section rings of the direct-image structure algebra

The extracted section algebra is canonically the original structure-sheaf ring
on the inverse-image open. The equivalence is the identity on elements and keeps
both the original scheme structure map and all presheaf restrictions. This avoids
requiring transported ring power operations to agree definitionally.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite
open scoped MonObj AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.Modules.Algebra

variable {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)

/-- The original structure-ring map gives the source sections their base algebra. -/
@[instance_reducible]
def inverseImageSectionsAlgebra : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

attribute [local instance] inverseImageSectionsAlgebra

/-- Extracted algebra sections are the original inverse-image structure-ring sections. -/
def pushforwardStructureSectionsAlgEquiv :
    Γ(pushforwardStructureSheaf f, U) ≃ₐ[Γ(X, U)] Γ(Y, f ⁻¹ᵁ U) := by
  let a : Γ(pushforwardStructureSheaf f, U) →ₐ[Γ(X, U)] Γ(Y, f ⁻¹ᵁ U) :=
    { toFun := fun m => m
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_one' := (f.app U).hom.map_one
      map_mul' := fun m n => pushforwardStructureMul_app f U m n
      commutes' := fun _ => rfl }
  exact AlgEquiv.ofBijective a ⟨fun _ _ h => h, fun m => ⟨m, rfl⟩⟩

/-- The comparison is literally the identity on the original section carrier. -/
@[simp] theorem pushforwardStructureSectionsAlgEquiv_apply
    (m : Γ(pushforwardStructureSheaf f, U)) :
    pushforwardStructureSectionsAlgEquiv f U m = m := rfl

/-- Its scalar map is the original structural ring map of the scheme morphism. -/
theorem pushforwardStructureSectionsAlgEquiv_algebraMap (r : Γ(X, U)) :
    pushforwardStructureSectionsAlgEquiv f U
      (algebraMap Γ(X, U) Γ(pushforwardStructureSheaf f, U) r) = (f.app U) r := rfl

/-- The comparison preserves the original structure-sheaf restrictions. -/
theorem pushforwardStructureSectionsAlgEquiv_restrict {U V : X.Opens} (i : V ⟶ U)
    (m : Γ(pushforwardStructureSheaf f, U)) :
    pushforwardStructureSectionsAlgEquiv f V
      (sectionRestriction (pushforwardStructureSheaf f) i m) =
      (Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op)
        (pushforwardStructureSectionsAlgEquiv f U m) := rfl

end AlgebraicGeometry.Scheme.Modules.Algebra
