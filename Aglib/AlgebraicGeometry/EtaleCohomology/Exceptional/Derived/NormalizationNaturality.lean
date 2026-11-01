/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Normalization
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.NaturalityInjectives
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Comparison

/-! # Original composite normalization preserves the original first-factor isomorphism -/
@[expose] public noncomputable section
open CategoryTheory
namespace CategoryTheory.Functor
universe u₁ u₂ u₃ v₁ v₂ v₃ d₁ d₂ d₃
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{d₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{d₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{d₃} C]
  (F F' : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [H.Additive]
  [F.PreservesInjectiveObjects] [F'.PreservesInjectiveObjects]

/-- Normalize after the original derived first-factor comparison, or before it. -/
theorem derivedCompositeNormalizeOfPreservesInjectives_changeFirst
    (e : F ≅ F') (t : F' ⋙ G ≅ H) :
    isoWhiskerRight (F.rightDerivedFunctorPlusIso e) G.rightDerivedFunctorPlus ≪≫
      derivedCompositeNormalizeOfPreservesInjectives F' G H t =
    derivedCompositeNormalizeOfPreservesInjectives F G H (isoWhiskerRight e G ≪≫ t) := by
  have h := rightDerivedFunctorPlusCompIsoOfPreservesInjectives_naturality_left G e
  have hn := congrArg (fun z =>
    (rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G).symm ≪≫ z ≪≫
      (rightDerivedFunctorPlusCompIsoOfPreservesInjectives F' G).symm) h
  simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl,
    Iso.symm_self_id_assoc] at hn
  simpa only [derivedCompositeNormalizeOfPreservesInjectives,
    rightDerivedFunctorPlusIso_trans, Iso.trans_assoc] using
    congrArg (fun z => z ≪≫ (F' ⋙ G).rightDerivedFunctorPlusIso t) hn.symm
end CategoryTheory.Functor
