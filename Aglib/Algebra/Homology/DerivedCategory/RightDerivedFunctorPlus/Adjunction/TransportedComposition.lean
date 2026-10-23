/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Composition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Comparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.NaturalityRight
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.NaturalityInjectives

/-! # Associativity after transporting the original composition comparisons -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄
namespace CategoryTheory.Functor
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  [EnoughInjectives C] {D : Type u₄} [Category.{v₄} D] [Abelian D]
  [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  (M : A ⥤ C) (N : B ⥤ D) (P : A ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [M.Additive] [N.Additive] [P.Additive]

/-- Any original associative composition comparison gives the same associative
comparison on the installed bounded-below derived functors. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportAssoc
    [G.PreservesHomology] [H.PreservesHomology] [N.PreservesHomology]
    [(G ⋙ H).PreservesHomology]
    (e₁ : P ≅ F ⋙ N) (e₂ : N ≅ G ⋙ H) (e₃ : P ≅ M ⋙ H) (e₄ : M ≅ F ⋙ G)
    (hc : e₁ ≪≫ isoWhiskerLeft F e₂ =
      e₃ ≪≫ isoWhiskerRight e₄ H ≪≫ associator F G H) :
    (P.rightDerivedFunctorPlusIso e₁ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology F N) ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus
          (N.rightDerivedFunctorPlusIso e₂ ≪≫
            rightDerivedFunctorPlusCompIsoOfPreservesHomology G H) =
      (P.rightDerivedFunctorPlusIso e₃ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology M H) ≪≫
        isoWhiskerRight (M.rightDerivedFunctorPlusIso e₄ ≪≫
          rightDerivedFunctorPlusCompIsoOfPreservesHomology F G) H.rightDerivedFunctorPlus ≪≫
        associator F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
          H.rightDerivedFunctorPlus := by
  let a := P.rightDerivedFunctorPlusIso e₁
  let b := rightDerivedFunctorPlusCompIsoOfPreservesHomology F N
  let c := isoWhiskerLeft F.rightDerivedFunctorPlus (N.rightDerivedFunctorPlusIso e₂)
  let d := isoWhiskerLeft F.rightDerivedFunctorPlus
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology G H)
  let e := (F ⋙ N).rightDerivedFunctorPlusIso (isoWhiskerLeft F e₂)
  let f := rightDerivedFunctorPlusCompIsoOfPreservesHomology F (G ⋙ H)
  let p := P.rightDerivedFunctorPlusIso e₃
  let q := (M ⋙ H).rightDerivedFunctorPlusIso (isoWhiskerRight e₄ H)
  let r := ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusIso (associator F G H)
  let s := rightDerivedFunctorPlusCompIsoOfPreservesHomology (F ⋙ G) H
  let t := isoWhiskerRight (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G)
    H.rightDerivedFunctorPlus
  let v := associator F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus H.rightDerivedFunctorPlus
  let k := rightDerivedFunctorPlusCompIsoOfPreservesHomology M H
  let l := isoWhiskerRight (M.rightDerivedFunctorPlusIso e₄) H.rightDerivedFunctorPlus
  have hr : b ≪≫ c = e ≪≫ f :=
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_right F e₂).symm
  have hl : q ≪≫ s = k ≪≫ l :=
    rightDerivedFunctorPlusCompIsoOfPreservesHomology_naturality_left H e₄
  have ha : r ≪≫ f ≪≫ d = s ≪≫ t ≪≫ v :=
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology_assoc F G H).symm
  have hp : a ≪≫ e = p ≪≫ q ≪≫ r := by
    simpa only [a, e, p, q, r, rightDerivedFunctorPlusIso_trans] using
      congrArg (fun z : P ≅ F ⋙ G ⋙ H => P.rightDerivedFunctorPlusIso z) hc
  simp only [isoWhiskerLeft_trans, isoWhiskerRight_trans, Iso.trans_assoc]
  change a ≪≫ b ≪≫ c ≪≫ d = p ≪≫ k ≪≫ l ≪≫ t ≪≫ v
  calc
    _ = a ≪≫ e ≪≫ f ≪≫ d := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => a ≪≫ z ≪≫ d) hr
    _ = p ≪≫ q ≪≫ r ≪≫ f ≪≫ d := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => z ≪≫ f ≪≫ d) hp
    _ = p ≪≫ q ≪≫ s ≪≫ t ≪≫ v := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => p ≪≫ q ≪≫ z) ha
    _ = p ≪≫ k ≪≫ l ≪≫ t ≪≫ v := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => p ≪≫ z ≪≫ t ≪≫ v) hl

/-- Any original associative composition comparison gives the same associative
comparison on the installed bounded-below derived functors. -/
theorem rightDerivedFunctorPlusCompIsoOfPreservesInjectives_transportAssoc
    [F.PreservesInjectiveObjects] [G.PreservesInjectiveObjects]
    [M.PreservesInjectiveObjects]
    (e₁ : P ≅ F ⋙ N) (e₂ : N ≅ G ⋙ H) (e₃ : P ≅ M ⋙ H) (e₄ : M ≅ F ⋙ G)
    (hc : e₁ ≪≫ isoWhiskerLeft F e₂ =
      e₃ ≪≫ isoWhiskerRight e₄ H ≪≫ associator F G H) :
    (P.rightDerivedFunctorPlusIso e₁ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives F N) ≪≫
        isoWhiskerLeft F.rightDerivedFunctorPlus
          (N.rightDerivedFunctorPlusIso e₂ ≪≫
            rightDerivedFunctorPlusCompIsoOfPreservesInjectives G H) =
      (P.rightDerivedFunctorPlusIso e₃ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives M H) ≪≫
        isoWhiskerRight (M.rightDerivedFunctorPlusIso e₄ ≪≫
          rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G) H.rightDerivedFunctorPlus ≪≫
        associator F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
          H.rightDerivedFunctorPlus := by
  let a := P.rightDerivedFunctorPlusIso e₁
  let b := rightDerivedFunctorPlusCompIsoOfPreservesInjectives F N
  let c := isoWhiskerLeft F.rightDerivedFunctorPlus (N.rightDerivedFunctorPlusIso e₂)
  let d := isoWhiskerLeft F.rightDerivedFunctorPlus
    (rightDerivedFunctorPlusCompIsoOfPreservesInjectives G H)
  let e := (F ⋙ N).rightDerivedFunctorPlusIso (isoWhiskerLeft F e₂)
  let f := rightDerivedFunctorPlusCompIsoOfPreservesInjectives F (G ⋙ H)
  let p := P.rightDerivedFunctorPlusIso e₃
  let q := (M ⋙ H).rightDerivedFunctorPlusIso (isoWhiskerRight e₄ H)
  let r := ((F ⋙ G) ⋙ H).rightDerivedFunctorPlusIso (associator F G H)
  let s := rightDerivedFunctorPlusCompIsoOfPreservesInjectives (F ⋙ G) H
  let t := isoWhiskerRight (rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G)
    H.rightDerivedFunctorPlus
  let v := associator F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus H.rightDerivedFunctorPlus
  let k := rightDerivedFunctorPlusCompIsoOfPreservesInjectives M H
  let l := isoWhiskerRight (M.rightDerivedFunctorPlusIso e₄) H.rightDerivedFunctorPlus
  have hr : b ≪≫ c = e ≪≫ f :=
    (rightDerivedFunctorPlusCompIsoOfPreservesInjectives_naturality_right F e₂).symm
  have hl : q ≪≫ s = k ≪≫ l :=
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives_naturality_left H e₄
  have ha : r ≪≫ f ≪≫ d = s ≪≫ t ≪≫ v :=
    (rightDerivedFunctorPlusCompIsoOfPreservesInjectives_assoc F G H).symm
  have hp : a ≪≫ e = p ≪≫ q ≪≫ r := by
    simpa only [a, e, p, q, r, rightDerivedFunctorPlusIso_trans] using
      congrArg (fun z : P ≅ F ⋙ G ⋙ H => P.rightDerivedFunctorPlusIso z) hc
  simp only [isoWhiskerLeft_trans, isoWhiskerRight_trans, Iso.trans_assoc]
  change a ≪≫ b ≪≫ c ≪≫ d = p ≪≫ k ≪≫ l ≪≫ t ≪≫ v
  calc
    _ = a ≪≫ e ≪≫ f ≪≫ d := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => a ≪≫ z ≪≫ d) hr
    _ = p ≪≫ q ≪≫ r ≪≫ f ≪≫ d := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => z ≪≫ f ≪≫ d) hp
    _ = p ≪≫ q ≪≫ s ≪≫ t ≪≫ v := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => p ≪≫ q ≪≫ z) ha
    _ = p ≪≫ k ≪≫ l ≪≫ t ≪≫ v := by
      simpa only [Iso.trans_assoc] using congrArg (fun z => p ≪≫ z ≪≫ t ≪≫ v) hl

end CategoryTheory.Functor
