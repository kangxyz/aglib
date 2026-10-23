/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Naturality

/-! # Naturality of the installed derived composition comparison -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  {F F' : A ⥤ B} [F.Additive] [F'.Additive]
  (G : B ⥤ C) [G.Additive]

/-- Naturality in the first factor, for the injective-preserving-first-factor comparison. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_naturality_left
    [F.PreservesInjectiveObjects] [F'.PreservesInjectiveObjects] (e : F ≅ F') :
    (F ⋙ G).rightDerivedFunctorPlusIso (isoWhiskerRight e G) ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives F' G =
      rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G ≪≫
        isoWhiskerRight (F.rightDerivedFunctorPlusIso e) G.rightDerivedFunctorPlus := by
  apply Iso.ext
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext (F ⋙ G).rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom,
    isoWhiskerRight_hom, whiskerRight_app]
  rw [← Category.assoc, rightDerivedFunctorPlusIso_hom_app, Category.assoc,
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app]
  conv_rhs =>
    rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app,
      Category.assoc, ← G.rightDerivedFunctorPlus.map_comp,
      rightDerivedFunctorPlusIso_hom_app, G.rightDerivedFunctorPlus.map_comp,
      ← Category.assoc]
  have hmap : (NatIso.mapCochainComplexPlus (isoWhiskerRight e G)).hom.app K =
      G.mapCochainComplexPlus.map ((NatIso.mapCochainComplexPlus e).hom.app K) := by
    apply ObjectProperty.hom_ext
    ext n
    rfl
  rw [hmap]
  simpa only [Category.assoc, comp_obj, comp_map] using congrArg
    (fun t => t ≫ G.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnit.app K))
    (G.rightDerivedFunctorPlusUnit.naturality
      ((NatIso.mapCochainComplexPlus e).hom.app K))

end CategoryTheory.Functor
