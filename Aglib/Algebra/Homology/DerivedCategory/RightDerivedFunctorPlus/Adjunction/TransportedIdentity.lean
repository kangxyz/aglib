/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.IdentityBranches
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.NaturalityRight
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.NaturalityInjectives
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Comparison

/-! # Unit coherence after transporting original functor comparisons -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w u' v' w'
namespace CategoryTheory.Functor
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [EnoughInjectives A] {B : Type u'} [Category.{v'} B] [Abelian B]
  [HasDerivedCategory.{w'} B] [EnoughInjectives B]
  (F P : A ⥤ B) [F.Additive] [P.Additive]

/-- A transported original right-unitor comparison remains the actual derived right unit. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportRightUnit
    (J : B ⥤ B) [J.Additive] [J.PreservesHomology]
    (e : P ≅ F ⋙ J) (eI : J ≅ 𝟭 B) :
    (P.rightDerivedFunctorPlusIso e ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F J) ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus
          (J.rightDerivedFunctorPlusIso eI ≪≫ rightDerivedFunctorPlusIdIso B) ≪≫
        rightUnitor F.rightDerivedFunctorPlus =
      P.rightDerivedFunctorPlusIso (e ≪≫ isoWhiskerLeft F eI ≪≫ rightUnitor F) := by
  let a := P.rightDerivedFunctorPlusIso e
  let b := rightDerivedFunctorPlusCompIsoOfPreservesHomology F J
  let c := isoWhiskerLeft F.rightDerivedFunctorPlus (J.rightDerivedFunctorPlusIso eI)
  let d := isoWhiskerLeft F.rightDerivedFunctorPlus (rightDerivedFunctorPlusIdIso B)
  let v := rightUnitor F.rightDerivedFunctorPlus
  let p := (F ⋙ J).rightDerivedFunctorPlusIso (isoWhiskerLeft F eI)
  let q := rightDerivedFunctorPlusCompIsoOfPreservesHomology F (𝟭 B)
  let r := (F ⋙ 𝟭 B).rightDerivedFunctorPlusIso (rightUnitor F)
  have hn : b ≪≫ c = p ≪≫ q :=
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_right F eI).symm
  have hu : q ≪≫ d ≪≫ v = r :=
    rightDerivedFunctorPlusCompIsoOfPreservesHomology_rightUnitor F
  simp only [isoWhiskerLeft_trans, Iso.trans_assoc, rightDerivedFunctorPlusIso_trans]
  change a ≪≫ b ≪≫ c ≪≫ d ≪≫ v = a ≪≫ p ≪≫ r
  calc
    _ = a ≪≫ p ≪≫ q ≪≫ d ≪≫ v := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => a ≪≫ z ≪≫ d ≪≫ v) hn
    _ = _ := congrArg (fun z => a ≪≫ p ≪≫ z) hu

omit [EnoughInjectives B] in
/-- A transported original left-unitor comparison remains the actual derived left unit. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportLeftUnit
    [F.PreservesHomology] (J : A ⥤ A) [J.Additive]
    (e : P ≅ J ⋙ F) (eI : J ≅ 𝟭 A) :
    (P.rightDerivedFunctorPlusIso e ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology J F) ≪≫
        isoWhiskerRight (J.rightDerivedFunctorPlusIso eI ≪≫ rightDerivedFunctorPlusIdIso A)
          F.rightDerivedFunctorPlus ≪≫ leftUnitor F.rightDerivedFunctorPlus =
      P.rightDerivedFunctorPlusIso (e ≪≫ isoWhiskerRight eI F ≪≫ leftUnitor F) := by
  let a := P.rightDerivedFunctorPlusIso e
  let b := rightDerivedFunctorPlusCompIsoOfPreservesHomology J F
  let c := isoWhiskerRight (J.rightDerivedFunctorPlusIso eI) F.rightDerivedFunctorPlus
  let d := isoWhiskerRight (rightDerivedFunctorPlusIdIso A) F.rightDerivedFunctorPlus
  let v := leftUnitor F.rightDerivedFunctorPlus
  let p := (J ⋙ F).rightDerivedFunctorPlusIso (isoWhiskerRight eI F)
  let q := rightDerivedFunctorPlusCompIsoOfPreservesHomology (𝟭 A) F
  let r := (𝟭 A ⋙ F).rightDerivedFunctorPlusIso (leftUnitor F)
  have hn : b ≪≫ c = p ≪≫ q :=
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_left F eI).symm
  have hu : q ≪≫ d ≪≫ v = r :=
    rightDerivedFunctorPlusCompIsoOfPreservesHomology_leftUnitor F
  simp only [isoWhiskerRight_trans, Iso.trans_assoc, rightDerivedFunctorPlusIso_trans]
  change a ≪≫ b ≪≫ c ≪≫ d ≪≫ v = a ≪≫ p ≪≫ r
  calc
    _ = a ≪≫ p ≪≫ q ≪≫ d ≪≫ v := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => a ≪≫ z ≪≫ d ≪≫ v) hn
    _ = _ := congrArg (fun z => a ≪≫ p ≪≫ z) hu

/-- A transported original right-unitor comparison remains the actual derived right unit. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_transportRightUnit
    [F.PreservesInjectiveObjects] (J : B ⥤ B) [J.Additive]
    (e : P ≅ F ⋙ J) (eI : J ≅ 𝟭 B) :
    (P.rightDerivedFunctorPlusIso e ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives F J) ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus
          (J.rightDerivedFunctorPlusIso eI ≪≫ rightDerivedFunctorPlusIdIso B) ≪≫
        rightUnitor F.rightDerivedFunctorPlus =
      P.rightDerivedFunctorPlusIso (e ≪≫ isoWhiskerLeft F eI ≪≫ rightUnitor F) := by
  let a := P.rightDerivedFunctorPlusIso e
  let b := rightDerivedFunctorPlusCompIsoOfPreservesInjectives F J
  let c := isoWhiskerLeft F.rightDerivedFunctorPlus (J.rightDerivedFunctorPlusIso eI)
  let d := isoWhiskerLeft F.rightDerivedFunctorPlus (rightDerivedFunctorPlusIdIso B)
  let v := rightUnitor F.rightDerivedFunctorPlus
  let p := (F ⋙ J).rightDerivedFunctorPlusIso (isoWhiskerLeft F eI)
  let q := rightDerivedFunctorPlusCompIsoOfPreservesInjectives F (𝟭 B)
  let r := (F ⋙ 𝟭 B).rightDerivedFunctorPlusIso (rightUnitor F)
  have hn : b ≪≫ c = p ≪≫ q :=
    (rightDerivedFunctorPlusCompIsoOfPreservesInjectives_naturality_right F eI).symm
  have hu : q ≪≫ d ≪≫ v = r :=
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives_rightUnitor F
  simp only [isoWhiskerLeft_trans, Iso.trans_assoc, rightDerivedFunctorPlusIso_trans]
  change a ≪≫ b ≪≫ c ≪≫ d ≪≫ v = a ≪≫ p ≪≫ r
  calc
    _ = a ≪≫ p ≪≫ q ≪≫ d ≪≫ v := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => a ≪≫ z ≪≫ d ≪≫ v) hn
    _ = _ := congrArg (fun z => a ≪≫ p ≪≫ z) hu

omit [EnoughInjectives B] in
/-- A transported original left-unitor comparison remains the actual derived left unit. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_transportLeftUnit
    (J : A ⥤ A) [J.Additive] [J.PreservesInjectiveObjects]
    (e : P ≅ J ⋙ F) (eI : J ≅ 𝟭 A) :
    (P.rightDerivedFunctorPlusIso e ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives J F) ≪≫
        isoWhiskerRight (J.rightDerivedFunctorPlusIso eI ≪≫ rightDerivedFunctorPlusIdIso A)
          F.rightDerivedFunctorPlus ≪≫ leftUnitor F.rightDerivedFunctorPlus =
      P.rightDerivedFunctorPlusIso (e ≪≫ isoWhiskerRight eI F ≪≫ leftUnitor F) := by
  let a := P.rightDerivedFunctorPlusIso e
  let b := rightDerivedFunctorPlusCompIsoOfPreservesInjectives J F
  let c := isoWhiskerRight (J.rightDerivedFunctorPlusIso eI) F.rightDerivedFunctorPlus
  let d := isoWhiskerRight (rightDerivedFunctorPlusIdIso A) F.rightDerivedFunctorPlus
  let v := leftUnitor F.rightDerivedFunctorPlus
  let p := (J ⋙ F).rightDerivedFunctorPlusIso (isoWhiskerRight eI F)
  let q := rightDerivedFunctorPlusCompIsoOfPreservesInjectives (𝟭 A) F
  let r := (𝟭 A ⋙ F).rightDerivedFunctorPlusIso (leftUnitor F)
  have hn : b ≪≫ c = p ≪≫ q :=
    (rightDerivedFunctorPlusCompIsoOfPreservesInjectives_naturality_left F eI).symm
  have hu : q ≪≫ d ≪≫ v = r :=
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives_leftUnitor F
  simp only [isoWhiskerRight_trans, Iso.trans_assoc, rightDerivedFunctorPlusIso_trans]
  change a ≪≫ b ≪≫ c ≪≫ d ≪≫ v = a ≪≫ p ≪≫ r
  calc
    _ = a ≪≫ p ≪≫ q ≪≫ d ≪≫ v := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => a ≪≫ z ≪≫ d ≪≫ v) hn
    _ = _ := congrArg (fun z => a ≪≫ p ≪≫ z) hu

end CategoryTheory.Functor
