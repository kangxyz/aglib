/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Linear
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# Actual structural linearity of scheme module sheaves

Global functions act by original module-linear multiplication on every module sheaf.
The resulting native category-center map supplies the linear category associated to any
specified structural ring map. Its morphism scalars are the original sectionwise scalars,
and its structure-module endomorphism is exactly the existing `unitMul`.
No quasicoherence, finiteness or Noetherianity is needed. The structural ring and scheme
universes are independent, and the ring map remains an explicit parameter.
Morphisms from the structure module are the global sections, linearly over any specified
structural ring map (`unitHomGlobalSectionsLinearEquivOfHom`).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- Original global functions map to the native center of the actual module-sheaf category. -/
abbrev globalScalarCenter : Γ(X, ⊤) →+* CatCenter X.Modules :=
  SheafOfModules.scalarCenterOfInitial X.sheaf (op ⊤) (isTerminalTop (α := X.Opens)).op

/-- The actual module-linear multiplication endomorphism of an arbitrary module sheaf. -/
abbrev globalScalarEndomorphism (M : X.Modules) (a : Γ(X, ⊤)) : M ⟶ M :=
  (globalScalarCenter X a).app M

/-- Original scalar multiplication restricts the original global function on every open. -/
theorem globalScalarEndomorphism_app (M : X.Modules) (a : Γ(X, ⊤))
    (U : X.Opens) (x : Γ(M, U)) :
    (globalScalarEndomorphism X M a).val.app (op U) x =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a • x := by
  change X.presheaf.map ((isTerminalTop (α := X.Opens)).op.to (op U)) a • x = _
  have he : (isTerminalTop (α := X.Opens)).op.to (op U) =
      (homOfLE (le_top : U ≤ ⊤)).op := Subsingleton.elim _ _
  rw [he]

/-- On the original structure module, the scalar-center action is the original `unitMul`. -/
theorem globalScalarEndomorphism_unit (a : Γ(X, ⊤)) :
    globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a = unitMul X a := by
  apply Scheme.Modules.hom_ext
  intro U
  ext b
  change Γ(X, U) at b
  change (globalScalarEndomorphism X (SheafOfModules.unit X.ringCatSheaf) a).val.app
      (op U) b = Scheme.Modules.Hom.app (unitMul X a) U b
  rw [globalScalarEndomorphism_app, unitMul_app]
  change (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a * b =
    b * (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a
  exact mul_comm ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom a) b

variable {R : Type v} [CommRing R] (α : R →+* Γ(X, ⊤))

/-- The actual module-sheaf category is linear over the specified structural ring map.
This explicit structure keeps different structural maps distinct. -/
abbrev moduleCategoryLinearOfHom : Linear R X.Modules :=
  Linear.ofRingMorphism ((globalScalarCenter X).comp α)

/-- Scalars of actual coefficient morphisms have the original sectionwise multiplication
formula for the specified structural ring map. -/
theorem moduleCategoryLinearOfHom_smul_app {M N : X.Modules} (φ : M ⟶ N)
    (r : R) (U : X.Opens) (x : Γ(M, U)) :
    letI := moduleCategoryLinearOfHom X α
    (r • φ).val.app (op U) x =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (α r) • φ.val.app (op U) x := by
  let := moduleCategoryLinearOfHom X α
  change φ.val.app (op U) ((globalScalarEndomorphism X M (α r)).val.app (op U) x) = _
  rw [globalScalarEndomorphism_app]
  exact (φ.val.app (op U)).hom.map_smul _ _

/-- Multiplication of the identity is the original module-linear scalar endomorphism. -/
theorem moduleCategoryLinearOfHom_smul_id (M : X.Modules) (r : R) :
    letI := moduleCategoryLinearOfHom X α
    r • 𝟙 M = globalScalarEndomorphism X M (α r) := by
  let := moduleCategoryLinearOfHom X α
  change globalScalarEndomorphism X M (α r) ≫ 𝟙 M = _
  exact Category.comp_id _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Morphisms from the structure module are the global sections, linearly over any specified
structural ring map; the forward map is evaluation on one (`unitHomGlobalSectionsAddEquiv`). -/
def unitHomGlobalSectionsLinearEquivOfHom (X : Scheme.{u}) {A : Type v} [CommRing A]
    (α : A →+* Γ(X, ⊤)) (M : X.Modules) :
    letI := moduleCategoryLinearOfHom X α
    letI : Module A (M.val.obj (op ⊤)) := Module.compHom _ α
    @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf) M ≃ₗ[A] M.val.obj (op ⊤) := by
  letI := moduleCategoryLinearOfHom X α
  letI : Module A (M.val.obj (op ⊤)) := Module.compHom _ α
  refine { __ := unitHomGlobalSectionsAddEquiv X M, map_smul' := fun a f => ?_ }
  change (a • f).val.app (op ⊤) (1 : Γ(X, ⊤)) = α a • f.val.app (op ⊤) (1 : Γ(X, ⊤))
  rw [moduleCategoryLinearOfHom_smul_app]
  have h : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := rfl
  rw [h, X.presheaf.map_id]
  rfl

theorem unitHomGlobalSectionsLinearEquivOfHom_apply (X : Scheme.{u}) {A : Type v} [CommRing A]
    (α : A →+* Γ(X, ⊤)) (M : X.Modules)
    (f : @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf) M) :
    unitHomGlobalSectionsLinearEquivOfHom X α M f = f.val.app (op ⊤) (1 : Γ(X, ⊤)) := rfl

end AlgebraicGeometry.Scheme.Modules
