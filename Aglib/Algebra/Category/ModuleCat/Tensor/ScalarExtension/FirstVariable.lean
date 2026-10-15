/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.Algebra.Category.ModuleCat.Tensor.ScalarExtension

/-!
# Naturality of scalar-compatible tensor transport in the extended module

The components are the original `scalarExtensionTensorIso`. Their naturality
in the first module argument gives the native tensor-right functor comparison,
retaining both the original extension map and its pure-tensor formula.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

/-- The original scalar-compatible tensor comparison is natural in the
extended module as well as in its other tensor argument. -/
@[reassoc]
theorem scalarExtensionTensorIso_naturality_left
    {A B : Type u} [CommRing A] [CommRing B] (α : A →+* B)
    {E E' : ModuleCat.{u} A} (g : E ⟶ E') (T : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars α).map ((ModuleCat.extendScalars α).map g ⊗ₘ 𝟙 T) ≫
        (scalarExtensionTensorIso α E' T).hom =
      (scalarExtensionTensorIso α E T).hom ≫
        (g ⊗ₘ 𝟙 ((ModuleCat.restrictScalars α).obj T)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul q t =>
    induction q using TensorProduct.inductionOn with
    | tmul b e =>
      change (scalarExtensionTensorIso α E' T).hom
          ((((ModuleCat.extendScalars α).map g)
            (b ⊗ₜ[A,α] e : (ModuleCat.extendScalars α).obj E)) ⊗ₜ[B] t) =
        (g ⊗ₘ 𝟙 ((ModuleCat.restrictScalars α).obj T))
          ((scalarExtensionTensorIso α E T).hom
            ((b ⊗ₜ[A,α] e : (ModuleCat.extendScalars α).obj E) ⊗ₜ[B] t))
      rw [ExtendScalars.map_tmul, scalarExtensionTensorIso_hom_tmul,
        scalarExtensionTensorIso_hom_tmul, ModuleCat.MonoidalCategory.tensorHom_tmul]
      rfl
    | add q q' h h' => simp only [TensorProduct.add_tmul, map_add, h, h']
  | add z z' h h' => simp only [map_add, h, h']

/-- Tensor-right transport uses the same original scalar-compatible components. -/
def scalarExtensionTensorFirstVariableNatIso
    {A B : Type u} [CommRing A] [CommRing B] (α : A →+* B) (T : ModuleCat.{u} B) :
    ModuleCat.extendScalars α ⋙ tensorRight T ⋙ ModuleCat.restrictScalars α ≅
      tensorRight ((ModuleCat.restrictScalars α).obj T) :=
  NatIso.ofComponents (fun E => scalarExtensionTensorIso α E T)
    (fun g => scalarExtensionTensorIso_naturality_left α g T)

/-- The first-variable natural comparison has the existing scalar tensor component. -/
@[simp]
theorem scalarExtensionTensorFirstVariableNatIso_app
    {A B : Type u} [CommRing A] [CommRing B] (α : A →+* B)
    (T : ModuleCat.{u} B) (E : ModuleCat.{u} A) :
    (scalarExtensionTensorFirstVariableNatIso α T).app E = scalarExtensionTensorIso α E T :=
  rfl

end ModuleCat
