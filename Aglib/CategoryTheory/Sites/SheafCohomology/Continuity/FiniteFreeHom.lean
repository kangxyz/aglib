/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FamilyProjective
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Colimits of Hom from finite free families of presheaves

The abelian-group-valued Hom functor from a finite free representable family
of PRESHEAVES preserves colimits. This is not a statement that evaluation of
sheaves preserves arbitrary colimits, or that free representable sheaves are
projective. The subsequent sheaf application must separately use preservation
of filtered colimits by the native sheaf-to-presheaf inclusion.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf.Cech

universe v u k

variable {C : Type u} [Category.{v} C]
  {ι : Type (max u v)} (U : ι → C)

/-- The original free-family Yoneda equivalence is additive. -/
def freeFamilyHomAddEquiv (A : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (familyPresheaf U ⋙ AddCommGrpCat.free ⟶ A) ≃+
      (∀ i, A.obj (op (U i))) where
  __ := freeFamilyHomEquiv U A
  map_add' f g := by
    funext i
    rfl

/-- The diagram of original presheaf evaluation functors. -/
abbrev familyEvaluationDiagram :
    Discrete ι ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ AddCommGrpCat.{max u v} :=
  Discrete.functor (fun i => (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op (U i)))

set_option backward.isDefEq.respectTransparency false in
/-- The additive Hom group from the actual free family is its product of sections. -/
def freeFamilyHomProductObjIso (A : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (preadditiveCoyoneda.obj (op (familyPresheaf U ⋙ AddCommGrpCat.free))).obj A ≅
      ((familyEvaluationDiagram U).flip ⋙ lim).obj A := by
  change AddCommGrpCat.of (familyPresheaf U ⋙ AddCommGrpCat.free ⟶ A) ≅ _
  exact (freeFamilyHomAddEquiv U A).toAddCommGrpIso ≪≫
    IsLimit.conePointUniqueUpToIso
      (AddCommGrpCat.HasLimit.productLimitCone (fun i => A.obj (op (U i)))).isLimit
      (limit.isLimit (Discrete.functor (fun i => A.obj (op (U i))))) ≪≫
    Pi.isoLimit ((familyEvaluationDiagram U).flip.obj A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Projection to a component is evaluation at its original free generator. -/
theorem freeFamilyHomProductObjIso_hom_π (A : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (i : ι) :
    (freeFamilyHomProductObjIso U A).hom ≫
        limit.π ((familyEvaluationDiagram U).flip.obj A) (Discrete.mk i) =
      AddCommGrpCat.ofHom
        { toFun := fun f => f.app (op (U i)) (FreeAbelianGroup.of ⟨i, 𝟙 _⟩)
          map_zero' := rfl
          map_add' := fun _ _ => rfl } := by
  dsimp only [freeFamilyHomProductObjIso, id, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, Pi.isoLimit_hom_π]
  exact congrArg
    (fun f => ((freeFamilyHomAddEquiv U A).toAddCommGrpIso :
      AddCommGrpCat.of (familyPresheaf U ⋙ AddCommGrpCat.free ⟶ A) ≅
        AddCommGrpCat.of (∀ j, A.obj (op (U j)))).hom ≫ f)
    (limit.conePointUniqueUpToIso_hom_comp
      (AddCommGrpCat.HasLimit.productLimitCone (fun j => A.obj (op (U j)))).isLimit
      (Discrete.mk i))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The finite-family Hom comparison is natural in the actual presheaf coefficient. -/
def freeFamilyHomProductIso :
    preadditiveCoyoneda.obj (op (familyPresheaf U ⋙ AddCommGrpCat.free)) ≅
      (familyEvaluationDiagram U).flip ⋙ lim :=
  NatIso.ofComponents (freeFamilyHomProductObjIso U) (by
    intro A B f
    apply limit.hom_ext
    intro ⟨i⟩
    change _ ≫ (freeFamilyHomProductObjIso U B).hom ≫ limit.π _ (Discrete.mk i) =
      (freeFamilyHomProductObjIso U A).hom ≫ limMap _ ≫ limit.π _ (Discrete.mk i)
    rw [limMap_π, freeFamilyHomProductObjIso_hom_π, ← Category.assoc,
      freeFamilyHomProductObjIso_hom_π]
    ext a
    rfl)

variable [Finite ι] {I : Type k} [SmallCategory I]
  [HasColimitsOfShape I AddCommGrpCat.{max u v}]

/-- In the presheaf category, Hom from a finite free family preserves all
colimits of the indicated shape, by finite biproducts and pointwise evaluation. -/
abbrev freeFamilyHomPreservesColimits :
    PreservesColimitsOfShape I
      (preadditiveCoyoneda.obj (op (familyPresheaf U ⋙ AddCommGrpCat.free))) := by
  let : PreservesColimitsOfShape I (familyEvaluationDiagram U).flip :=
    preservesColimitsOfShape_of_evaluation _ _ (fun i => by
      change PreservesColimitsOfShape I
        ((evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op (U i.as)))
      infer_instance)
  let : PreservesColimitsOfShape I
      (lim (J := Discrete ι) (C := AddCommGrpCat.{max u v})) :=
    preservesColimitsOfShape_of_natIso HasBiproductsOfShape.colimIsoLim
  exact preservesColimitsOfShape_of_natIso (freeFamilyHomProductIso U).symm

end CategoryTheory.Presheaf.Cech
