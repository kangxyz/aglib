/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.HomLifts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FixedTargetData
public import Mathlib.CategoryTheory.Filtered.Connected

/-! # Actual maps between fixed native module models

The actual fixed-coefficient colimit comparison turns a representative in the
native right-tail Hom cocone into a later map between the two original model
pullbacks. Its conclusion retains the original inverse-image triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u

open FixedModelData

variable (R : Type (u + 1)) [Ring R]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (i : I)
    (r : (Functor.const I).obj (X.obj i) ⟶ X) (hr : r.app i = 𝟙 (X.obj i))
    (c : Cocone X) (hc : IsColimit c)

variable [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop]

include hr hc in
/-- Every original map between pulled-back native models has a later native
representative, with the exact original comparison equation. -/
theorem exists_baseHom
    (A : Coefficient R (X.obj i).unop)
    (hA : Constructible.Modules.NativeFreePresentation.finiteColimitStages R (X.obj i).unop A)
    (B : Coefficient R (X.obj i).unop)
    [HasColimit (coneCoefficientFunctor R X c
      (pullbackCoefficientSystem R X (Cone.mk (X.obj i) r) B))]
    (γ : (inverseImage R (c.ι.app i).unop).obj A ⟶
      (inverseImage R (c.ι.app i).unop).obj B) :
    ∃ (a : Under i)
      (β : (inverseImage R (X.map a.hom).unop).obj A ⟶
        (inverseImage R (X.map a.hom).unop).obj B),
      ((schemeAdjunctionData R).triangleIso (c.ι.app i) (X.map a.hom)
          (c.ι.app a.right) (c.w a.hom)).hom.app A ≫
        (inverseImage R (c.ι.app a.right).unop).map β =
      γ ≫ ((schemeAdjunctionData R).triangleIso (c.ι.app i) (X.map a.hom)
          (c.ι.app a.right) (c.w a.hom)).hom.app B := by
  let F : DiagramCoefficientSystem R X := pullbackCoefficientSystem R X (Cone.mk (X.obj i) r) B
  let E := FixedModelData.limitIso R X i r hr c B
  obtain ⟨a, β, hβ⟩ :=
    Constructible.Modules.NativeFreePresentation.exists_originalRightTailHom
      R X c F hc i A hA (γ ≫ E.inv)
  let eB : F.obj a.right ≅ (inverseImage R (X.map a.hom).unop).obj B :=
    eqToIso (congrArg (fun q : X.obj i ⟶ X.obj a.right => (inverseImage R q.unop).obj B)
      (cone_identity_leg X i r hr a.hom))
  let T : inverseImage R (c.ι.app i).unop ≅
      inverseImage R (X.map a.hom).unop ⋙ inverseImage R (c.ι.app a.right).unop :=
    (schemeAdjunctionData R).triangleIso (c.ι.app i) (X.map a.hom)
    (c.ι.app a.right) (c.w a.hom)
  have hins : colimit.ι (coneCoefficientFunctor R X c F) a.right ≫ E.hom =
      ((schemeAdjunctionData R).triangleIso (c.ι.app i) (r.app a.right)
        (c.ι.app a.right) (baseCone_fac X i r hr c a.right)).inv.app B :=
    FixedModelData.limitIso_ι R X i r hr c B a.right
  have ht : (inverseImage R (c.ι.app a.right).unop).map eB.hom ≫ T.inv.app B =
      ((schemeAdjunctionData R).triangleIso (c.ι.app i) (r.app a.right)
        (c.ι.app a.right) (baseCone_fac X i r hr c a.right)).inv.app B :=
    triangle_target_transport (schemeAdjunctionData R) _ _ _ _
      (baseCone_fac X i r hr c a.right) (c.w a.hom)
      (cone_identity_leg X i r hr a.hom) B
  have htriangle : (diagramConeAdjunctionData R X c).leftTriangle a.hom = T :=
    ((schemeAdjunctionData R).triangleIso_eq_leftAdjointCompIso
      (c.ι.app i) (X.map a.hom) (c.ι.app a.right) (c.w a.hom)).symm
  have hβ' : (T.hom.app A ≫ (inverseImage R (c.ι.app a.right).unop).map β) ≫
      colimit.ι (coneCoefficientFunctor R X c F) a.right = γ ≫ E.inv :=
    (congrArg (fun e : inverseImage R (c.ι.app i).unop ≅
        inverseImage R (X.map a.hom).unop ⋙ inverseImage R (c.ι.app a.right).unop =>
      (e.hom.app A ≫
      (inverseImage R (c.ι.app a.right).unop).map β) ≫
        colimit.ι (coneCoefficientFunctor R X c F) a.right) htriangle).symm.trans hβ
  exact ⟨a, β ≫ eB.hom,
    AdjointStageHom.factorization_target_iso (inverseImage R (c.ι.app a.right).unop)
      (T.hom.app A) β eB (T.app B) E
      (colimit.ι (coneCoefficientFunctor R X c F) a.right) γ _ hins ht hβ'⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
