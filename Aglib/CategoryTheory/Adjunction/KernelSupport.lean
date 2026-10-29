/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Support subobjects from a chosen family of adjunctions

Intersect the kernels of the original units outside a specified index set.
The construction keeps the native bounded infimum and its chosen subobject
inclusion. An outside left adjoint kills this subobject whenever it preserves
monomorphisms: map the zero unit-composite and apply the adjunction triangle.
-/

@[expose] public noncomputable section

universe w i v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open Limits

variable {I : Type i} {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D]
  [LocallySmall.{w} C] [WellPowered.{w} C] [HasWidePullbacks.{w} C]
  {L : I → C ⥤ D} {R : I → D ⥤ C} (adj : ∀ i, L i ⊣ R i) (F : C)

/-- The subobject annihilated by the chosen units outside the indicated index set. -/
def kernelSupport (Z : Set I) : Subobject F :=
  Subobject.sInf.{w} (Set.range (fun i : {i : I // i ∉ Z} =>
    kernelSubobject ((adj i.val).unit.app F)))

/-- Enlarging the support set gives the canonical inequality of support subobjects. -/
theorem kernelSupport_mono {Z W : Set I} (h : Z ⊆ W) :
    kernelSupport adj F Z ≤ kernelSupport adj F W := by
  apply Subobject.le_sInf.{w}
  rintro _ ⟨i, rfl⟩
  exact Subobject.sInf_le.{w} _ _
    ⟨⟨i.val, fun hi => i.property (h hi)⟩, rfl⟩

private theorem kernelSupport_le_kernel (Z : Set I) (i : I) (hi : i ∉ Z) :
    kernelSupport adj F Z ≤ kernelSubobject ((adj i).unit.app F) :=
  Subobject.sInf_le.{w} _ _ ⟨⟨i, hi⟩, rfl⟩

/-- The actual support inclusion is killed by every outside unit. -/
theorem kernelSupport_arrow_unit (Z : Set I) (i : I) (hi : i ∉ Z) :
    (kernelSupport adj F Z).arrow ≫ (adj i).unit.app F = 0 := by
  rw [← Subobject.ofLE_arrow (kernelSupport_le_kernel adj F Z i hi),
    Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-- A morphism factors through the support subobject exactly when all its
outside unit-composites vanish. -/
theorem kernelSupport_factors_iff (Z : Set I) {A : C} (a : A ⟶ F) :
    (kernelSupport adj F Z).Factors a ↔
      ∀ i : I, i ∉ Z → a ≫ (adj i).unit.app F = 0 := by
  constructor
  · intro h i hi
    rw [← Subobject.factorThru_arrow _ _ h, Category.assoc,
      kernelSupport_arrow_unit adj F Z i hi, comp_zero]
  · intro h
    have hi : imageSubobject a ≤ kernelSupport adj F Z := by
      apply Subobject.le_sInf.{w}
      rintro _ ⟨i, rfl⟩
      exact le_kernelSubobject _ _ (imageSubobject_arrow_comp_eq_zero (h i.val i.property))
    apply (Subobject.factors_iff _ _).mpr
    refine ⟨factorThruImageSubobject a ≫ Subobject.ofLE _ _ hi, ?_⟩
    change (factorThruImageSubobject a ≫ Subobject.ofLE _ _ hi) ≫
      (kernelSupport adj F Z).arrow = a
    rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]

/-- The native chosen factor through the support subobject has its original composite. -/
theorem kernelSupport_factorThru_arrow (Z : Set I) {A : C} (a : A ⟶ F)
    (h : ∀ i : I, i ∉ Z → a ≫ (adj i).unit.app F = 0) :
    (kernelSupport adj F Z).factorThru a ((kernelSupport_factors_iff adj F Z a).mpr h) ≫
      (kernelSupport adj F Z).arrow = a :=
  Subobject.factorThru_arrow _ _ _

/-- An outside left adjoint that preserves monomorphisms sends the actual
support subobject to zero. No preservation of its infimum is required. -/
theorem kernelSupport_outside [HasZeroMorphisms D] (Z : Set I) (i : I) (hi : i ∉ Z)
    [(L i).PreservesMonomorphisms] :
    IsZero ((L i).obj (kernelSupport adj F Z : C)) := by
  let : (L i).IsLeftAdjoint := (adj i).isLeftAdjoint
  let a := (kernelSupport adj F Z).arrow
  have hz := kernelSupport_arrow_unit adj F Z i hi
  have h := congrArg (fun q => (L i).map q ≫ (adj i).counit.app ((L i).obj F)) hz
  have ht : (L i).map ((adj i).unit.app F) ≫
      (adj i).counit.app ((L i).obj F) = 𝟙 ((L i).obj F) :=
    (adj i).left_triangle_components F
  have hm : (L i).map a = 0 := by
    change (L i).map (a ≫ (adj i).unit.app F) ≫
      (adj i).counit.app ((L i).obj F) = (L i).map 0 ≫ _ at h
    simpa only [Functor.map_comp, Category.assoc, ht, Category.comp_id,
      Functor.map_zero, zero_comp] using h
  let : Mono a := inferInstanceAs (Mono (kernelSupport adj F Z).arrow)
  exact IsZero.of_mono_eq_zero ((L i).map a) hm

end CategoryTheory.Adjunction
