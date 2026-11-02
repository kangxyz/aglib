/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactCompositeUnit

/-!
# Source-identity contraction of an original localized exact square

A specified ordinary square contracts through its original source identity
comparison to a specified ordinary triangle. The same equation holds for the
native full derived square and triangle, with the localized original identity
and the native derived identity comparison. The proof uses all-complex
localization coherence, not restriction to bounded-below objects.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits

universe uA vA wA uB vB wB uC vC wC

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  (F : A ⥤ B) (H : B ⥤ C) (V : A ⥤ C) (J : A ⥤ A)
  [F.Additive] [H.Additive] [V.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
  (e : F ⋙ H ≅ J ⋙ V) (d : J ≅ 𝟭 A) (σ : F ⋙ H ≅ V)
  (hσ : σ = e ≪≫ isoWhiskerRight d V ≪≫ leftUnitor V)

include hσ

/-- The original localized square contracts to the original localized triangle
through the specified source identity, as a whole natural-isomorphism equation. -/
theorem mapDerivedCategorySquareIso_source_identity :
    mapDerivedCategoryTriangleIso F H V σ =
      mapDerivedCategorySquareIso J V F H e ≪≫
        isoWhiskerRight (mapDerivedCategoryOriginalIso J (𝟭 A) d ≪≫
          mapDerivedCategoryIdIso A) V.mapDerivedCategory ≪≫
        leftUnitor V.mapDerivedCategory := by
  have hi := mapDerivedCategoryTriangleIso_left_id J V
    (isoWhiskerRight d V ≪≫ leftUnitor V) d rfl
  rw [← hi, hσ]
  simp only [mapDerivedCategoryTriangleIso, mapDerivedCategorySquareIso,
    mapDerivedCategoryOriginalIso_trans, Iso.trans_assoc, Iso.symm_self_id_assoc]
  rfl

/-- The same contraction retains the actual component square and original
identity map on every unbounded native derived object. -/
theorem mapDerivedCategorySquareIso_source_identity_hom_app (K : DerivedCategory A) :
    (mapDerivedCategoryTriangleIso F H V σ).hom.app K =
      (mapDerivedCategorySquareIso J V F H e).hom.app K ≫
        V.mapDerivedCategory.map
          ((mapDerivedCategoryOriginalIso J (𝟭 A) d ≪≫
            mapDerivedCategoryIdIso A).hom.app K) := by
  have h := congrArg (fun z => z.hom.app K)
    (mapDerivedCategorySquareIso_source_identity F H V J e d σ hσ)
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    whiskerRight_app, leftUnitor_hom_app] at h
  erw [Category.comp_id] at h
  exact h

end CategoryTheory.Functor
