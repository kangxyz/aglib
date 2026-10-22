/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_

/-! # Algebra operations detected by the original quotient maps

These arguments take place in the native monoidal category before any sheaf
or completion is substituted. They require joint detection only on the unit,
underlying object, and the two tensor powers which actually occur.
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped MonObj

namespace CategoryTheory

universe v u w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {ι : Type w} {M : C} {F : ι → C} (q : ∀ i, M ⟶ F i)

/-- Equality of maps into `M` can be tested after the specified family. -/
def JointlyDetects (P : C) : Prop :=
  ∀ a b : P ⟶ M, (∀ i, a ≫ q i = b ≫ q i) → a = b

omit [MonoidalCategory C] in
/-- Transport the source of a joint-detection test along an actual isomorphism. -/
theorem JointlyDetects.ofIso {P Q : C} (h : JointlyDetects q P) (e : P ≅ Q) :
    JointlyDetects q Q := by
  intro a b hab
  apply (cancel_epi e.hom).mp
  exact h _ _ fun i => by
    simpa only [Category.assoc] using congrArg (fun k => e.hom ≫ k) (hab i)

/-- Reconstruct all monoid laws from operation-preserving maps and precisely
three source-detection statements. -/
@[instance_reducible]
def monObjOfJointDetection [∀ i, MonObj (F i)]
    (one : 𝟙_ C ⟶ M) (mul : M ⊗ M ⟶ M)
    (hOne : ∀ i, one ≫ q i = η[F i])
    (hMul : ∀ i, mul ≫ q i = (q i ⊗ₘ q i) ≫ μ[F i])
    (hM : JointlyDetects q M)
    (hTriple : JointlyDetects q ((M ⊗ M) ⊗ M)) : MonObj M where
  one := one
  mul := mul
  one_mul := by
    apply JointlyDetects.ofIso q hM (λ_ M).symm
    intro i
    simp only [Category.assoc, hMul, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, hOne]
    simp [tensorHom_def']
  mul_one := by
    apply JointlyDetects.ofIso q hM (ρ_ M).symm
    intro i
    simp only [Category.assoc, hMul, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, hOne]
    simp [tensorHom_def]
  mul_assoc := by
    apply hTriple
    intro i
    simp only [Category.assoc, hMul, ← tensorHom_id, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.id_comp]
    simpa only [Category.assoc, ← tensorHom_id, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp,
      associator_naturality_assoc] using
      congrArg (fun k => ((q i ⊗ₘ q i) ⊗ₘ q i) ≫ k) (MonObj.mul_assoc (F i))

variable [BraidedCategory C]

/-- The entire native algebra and original-map certificate is constructed
before geometric specialization. -/
structure JointDetectionCommMonData [∀ i, MonObj (F i)] where
  /-- The reconstructed native multiplication and unit on the original object. -/
  mon : MonObj M
  comm : @IsCommMonObj C _ _ _ M mon
  map : ∀ i, @IsMonHom C _ _ M (F i) mon inferInstance (q i)

/-- Commutativity and all the original algebra-map equations are retained
with the reconstructed native monoid structure. -/
def commMonOfJointDetection [∀ i, MonObj (F i)] [∀ i, IsCommMonObj (F i)]
    (one : 𝟙_ C ⟶ M) (mul : M ⊗ M ⟶ M)
    (hOne : ∀ i, one ≫ q i = η[F i])
    (hMul : ∀ i, mul ≫ q i = (q i ⊗ₘ q i) ≫ μ[F i])
    (hM : JointlyDetects q M)
    (hTensor : JointlyDetects q (M ⊗ M))
    (hTriple : JointlyDetects q ((M ⊗ M) ⊗ M)) : JointDetectionCommMonData q := by
  let mon := monObjOfJointDetection q one mul hOne hMul hM hTriple
  letI : MonObj M := mon
  refine ⟨mon, ⟨?_⟩, fun i => ⟨hOne i, hMul i⟩⟩
  change (β_ M M).hom ≫ mul = mul
  apply hTensor
  intro i
  rw [Category.assoc, hMul, ← BraidedCategory.braiding_naturality_assoc]
  simp

omit [BraidedCategory C] in
/-- A proposed algebra map is an algebra map whenever its composites with
jointly detecting algebra maps are algebra maps. -/
theorem isMonHom_of_jointDetection {N : C} [MonObj M] [MonObj N]
    [∀ i, MonObj (F i)] [∀ i, IsMonHom (q i)]
    (f : N ⟶ M) [∀ i, IsMonHom (f ≫ q i)]
    (hUnit : JointlyDetects q (𝟙_ C))
    (hTensor : JointlyDetects q (N ⊗ N)) : IsMonHom f where
  one_hom := by
    apply hUnit
    intro i
    simp only [Category.assoc, IsMonHom.one_hom]
  mul_hom := by
    apply hTensor
    intro i
    simp only [Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc]

end CategoryTheory
