/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExactDerivedContractionModels
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Naturality
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Comparison
/-! # Original contraction naturality in the first factor -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace DerivedCategory.Plus
universe u v d u' v' d'
variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{d} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{d'} B]
  {F F' : A ⥤ B} (G : B ⥤ A) [F.Additive] [F'.Additive] [G.Additive]
  [G.PreservesHomology] (e : F ≅ F') (c : F' ⋙ G ≅ 𝟭 A)

/-- Native deriving of the original first-factor iso preserves the original contraction. -/
theorem exactDerivedContractionViaIso_naturality :
    isoWhiskerRight (F.rightDerivedFunctorPlusIso e) G.rightDerivedFunctorPlus ≪≫
      exactDerivedContractionViaIso F' G c =
    exactDerivedContractionViaIso F G (isoWhiskerRight e G ≪≫ c) := by
  have hn := rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_left G e
  have h : isoWhiskerRight (F.rightDerivedFunctorPlusIso e) G.rightDerivedFunctorPlus ≪≫
      (rightDerivedFunctorPlusCompIsoOfPreservesHomology F' G).symm =
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).symm ≪≫
      (F ⋙ G).rightDerivedFunctorPlusIso (isoWhiskerRight e G) := by
    have h' := congrArg (fun z =>
      (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).symm ≪≫ z ≪≫
        (rightDerivedFunctorPlusCompIsoOfPreservesHomology F' G).symm) hn
    simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc,
      Iso.self_symm_id, Iso.trans_refl] using h'.symm
  unfold exactDerivedContractionViaIso
  rw [rightDerivedFunctorPlusIso_trans, ← Iso.trans_assoc, h]
  simp only [Iso.trans_assoc]
end DerivedCategory.Plus
