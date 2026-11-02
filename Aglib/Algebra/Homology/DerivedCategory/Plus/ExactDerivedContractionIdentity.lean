/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ExactDerivedContractionModels
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedIdentity

/-! # Original contraction through the endpoint model and the native identity comparisons -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace DerivedCategory.Plus
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{w} A]
  (F G : A ⥤ A) [F.Additive] [G.Additive] [G.PreservesHomology]
  (eF : F ≅ 𝟭 A) (eG : G ≅ 𝟭 A)

/-- The original native contraction is the product of the original derived identities. -/
theorem exactDerivedContractionViaIso_identity :
    exactDerivedContractionViaIso F G
        ((isoWhiskerRight eF G ≪≫ leftUnitor G) ≪≫ eG) =
      isoWhiskerRight (F.rightDerivedFunctorPlusIso eF ≪≫ rightDerivedFunctorPlusIdIso A)
        G.rightDerivedFunctorPlus ≪≫ leftUnitor G.rightDerivedFunctorPlus ≪≫
        (G.rightDerivedFunctorPlusIso eG ≪≫ rightDerivedFunctorPlusIdIso A) := by
  have h := rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportLeftUnit
    G (F ⋙ G) F (Iso.refl _) eF
  simp only [rightDerivedFunctorPlusIso_refl, Iso.refl_trans] at h
  unfold exactDerivedContractionViaIso
  rw [rightDerivedFunctorPlusIso_trans, ← h]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]

end DerivedCategory.Plus
