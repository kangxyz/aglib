/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar-compatible tensor transport for arbitrary coefficients
-/

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/ScalarExtensionTensor.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Selection: whole_general; source ranges [[1, 89]].
Actual objects, maps, universes and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- Restricting the tensor with an extended coefficient is tensor with the restricted module. -/
def scalarExtensionTensorIso {A B : Type u} [CommRing A] [CommRing B] (α : A →+* B)
    (E : ModuleCat.{u} A) (T : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars α).obj ((ModuleCat.extendScalars α).obj E ⊗ T) ≅
      E ⊗ (ModuleCat.restrictScalars α).obj T := by
  letI := α.toAlgebra
  let T' := (ModuleCat.restrictScalars α).obj T
  letI : IsScalarTower A B T' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : SMulCommClass A B T' := ⟨fun a b t => by
    change α a • (b • (t : T)) = b • (α a • (t : T))
    exact smul_comm _ _ _⟩
  let e := (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B T' E).restrictScalars A
  exact (ModuleCat.restrictScalars α).mapIso (β_ ((ModuleCat.extendScalars α).obj E) T) ≪≫
    e.toModuleIso ≪≫ β_ T' E

/-- The scalar transport keeps multiplication by the original extended scalar. -/
theorem scalarExtensionTensorIso_hom_tmul {A B : Type u} [CommRing A] [CommRing B]
    (α : A →+* B) (E : ModuleCat.{u} A) (T : ModuleCat.{u} B)
    (b : B) (e : E) (t : T) :
    (scalarExtensionTensorIso α E T).hom
        ((b ⊗ₜ[A,α] e : (ModuleCat.extendScalars α).obj E) ⊗ₜ[B] t) =
      e ⊗ₜ[A] (show (ModuleCat.restrictScalars α).obj T from b • t) := rfl

/-- The inverse uses the unit scalar of the original scalar extension. -/
theorem scalarExtensionTensorIso_inv_tmul {A B : Type u} [CommRing A] [CommRing B]
    (α : A →+* B) (E : ModuleCat.{u} A) (T : ModuleCat.{u} B)
    (e : E) (t : (ModuleCat.restrictScalars α).obj T) :
    (scalarExtensionTensorIso α E T).inv (e ⊗ₜ[A] t) =
      (((1 : B) ⊗ₜ[A,α] e : (ModuleCat.extendScalars α).obj E) ⊗ₜ[B] (show T from t)) := rfl

/-- Naturality for the unchanged module map in the tensor's second variable. -/
theorem scalarExtensionTensorIso_naturality {A B : Type u} [CommRing A] [CommRing B]
    (α : A →+* B) (E : ModuleCat.{u} A) {T T' : ModuleCat.{u} B} (g : T ⟶ T') :
    (ModuleCat.restrictScalars α).map (𝟙 ((ModuleCat.extendScalars α).obj E) ⊗ₘ g) ≫
        (scalarExtensionTensorIso α E T').hom =
      (scalarExtensionTensorIso α E T).hom ≫
        (𝟙 E ⊗ₘ (ModuleCat.restrictScalars α).map g) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul q t =>
    induction q using TensorProduct.inductionOn with
    | tmul b e =>
      change (scalarExtensionTensorIso α E T').hom
          ((b ⊗ₜ[A,α] e : (ModuleCat.extendScalars α).obj E) ⊗ₜ[B] g t) =
        (𝟙 E ⊗ₘ (ModuleCat.restrictScalars α).map g)
          ((scalarExtensionTensorIso α E T).hom
            ((b ⊗ₜ[A,α] e : (ModuleCat.extendScalars α).obj E) ⊗ₜ[B] t))
      rw [scalarExtensionTensorIso_hom_tmul, scalarExtensionTensorIso_hom_tmul,
        ModuleCat.MonoidalCategory.tensorHom_tmul]
      exact congrArg (fun w => e ⊗ₜ[A] (show (ModuleCat.restrictScalars α).obj T' from w))
        (g.hom.map_smul b t).symm
    | add q q' h h' => simp only [TensorProduct.add_tmul, map_add, h, h']
  | add z z' h h' => simp only [map_add, h, h']

/-- A natural tensor comparison after the literal extension and restriction of scalars. -/
def scalarExtensionTensorNatIso {A B : Type u} [CommRing A] [CommRing B] (α : A →+* B)
    (E : ModuleCat.{u} A) :
    tensorLeft ((ModuleCat.extendScalars α).obj E) ⋙ ModuleCat.restrictScalars α ≅
      ModuleCat.restrictScalars α ⋙ tensorLeft E :=
  NatIso.ofComponents (scalarExtensionTensorIso α E)
    (fun g => scalarExtensionTensorIso_naturality α E g)

end ModuleCat
