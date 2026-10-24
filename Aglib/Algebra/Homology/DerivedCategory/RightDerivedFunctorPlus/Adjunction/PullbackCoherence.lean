/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedIdentity

/-! # Coherence of original pullback comparisons on bounded-below derived categories

The displayed comparisons are the inverse native composition comparisons followed
by the derived images of the original isomorphisms. Their composition and identity
laws follow from the corresponding original laws, without a new choice of functor
or comparison isomorphism.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

namespace CategoryTheory.Functor

section Comparison

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] (F : A ⥤ B) [F.Additive]

/-- Deriving the inverse original isomorphism gives the inverse installed comparison. -/
@[simp]
theorem rightDerivedFunctorPlusIso_symm {G : A ⥤ B} [G.Additive] (e : F ≅ G) :
    G.rightDerivedFunctorPlusIso e.symm = (F.rightDerivedFunctorPlusIso e).symm := by
  have h := congrArg (fun z : F ≅ F => F.rightDerivedFunctorPlusIso z)
    (Iso.self_symm_id e)
  rw [rightDerivedFunctorPlusIso_trans, rightDerivedFunctorPlusIso_refl] at h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.trans_refl] using
    congrArg (fun z => (F.rightDerivedFunctorPlusIso e).symm ≪≫ z) h

end Comparison

section Composition

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]
  [EnoughInjectives C] {D : Type u₄} [Category.{v₄} D] [Abelian D]
  [HasDerivedCategory.{w₄} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  (M : A ⥤ C) (N : B ⥤ D) (P : A ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [M.Additive] [N.Additive] [P.Additive]

/-- An original pullback composition law gives the same exact law for the installed
bounded-below derived comparisons. Homology preservation is required only for the
three functors on the right of the original comparisons. -/
theorem rightDerivedFunctorPlusPullbackIso_comp
    [G.PreservesHomology] [H.PreservesHomology] [N.PreservesHomology]
    (σf : F ⋙ G ≅ M) (σk : M ⋙ H ≅ P) (σt : F ⋙ N ≅ P) (c : N ≅ G ⋙ H)
    (hc : σt = isoWhiskerLeft F c ≪≫ (associator F G H).symm ≪≫
      isoWhiskerRight σf H ≪≫ σk) :
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology F N).symm ≪≫
        (F ⋙ N).rightDerivedFunctorPlusIso σt =
      isoWhiskerLeft F.rightDerivedFunctorPlus
          (N.rightDerivedFunctorPlusIso c ≪≫
            rightDerivedFunctorPlusCompIsoOfPreservesHomology G H) ≪≫
        (associator F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
          H.rightDerivedFunctorPlus).symm ≪≫
        isoWhiskerRight
          ((rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).symm ≪≫
            (F ⋙ G).rightDerivedFunctorPlusIso σf) H.rightDerivedFunctorPlus ≪≫
        (rightDerivedFunctorPlusCompIsoOfPreservesHomology M H).symm ≪≫
        (M ⋙ H).rightDerivedFunctorPlusIso σk := by
  let : Limits.PreservesFiniteLimits G := G.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits G := G.preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits H := H.preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits H := H.preservesFiniteColimits_of_preservesHomology
  let : (G ⋙ H).PreservesHomology := inferInstance
  have hc' : σt.symm ≪≫ isoWhiskerLeft F c =
      σk.symm ≪≫ isoWhiskerRight σf.symm H ≪≫ associator F G H := by
    simp only [hc, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
      Iso.symm_self_id, Iso.trans_refl, isoWhiskerRight_symm]
  have h := rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportAssoc
    F G H M N P σt.symm c σk.symm σf.symm hc'
  let fD := (rightDerivedFunctorPlusCompIsoOfPreservesHomology F G).symm ≪≫
    (F ⋙ G).rightDerivedFunctorPlusIso σf
  let kD := (rightDerivedFunctorPlusCompIsoOfPreservesHomology M H).symm ≪≫
    (M ⋙ H).rightDerivedFunctorPlusIso σk
  let tD := (rightDerivedFunctorPlusCompIsoOfPreservesHomology F N).symm ≪≫
    (F ⋙ N).rightDerivedFunctorPlusIso σt
  let cD := isoWhiskerLeft F.rightDerivedFunctorPlus
    (N.rightDerivedFunctorPlusIso c ≪≫
      rightDerivedFunctorPlusCompIsoOfPreservesHomology G H)
  have hD : tD.symm ≪≫ cD = kD.symm ≪≫
      (isoWhiskerRight fD H.rightDerivedFunctorPlus).symm ≪≫
      associator F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
        H.rightDerivedFunctorPlus := by
    simpa only [fD, kD, tD, cD, Iso.trans_symm, Iso.symm_symm_eq,
      rightDerivedFunctorPlusIso_symm, isoWhiskerRight_symm] using h
  change tD = cD ≪≫
    (associator F.rightDerivedFunctorPlus G.rightDerivedFunctorPlus
      H.rightDerivedFunctorPlus).symm ≪≫
    isoWhiskerRight fD H.rightDerivedFunctorPlus ≪≫ kD
  simpa only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
    Iso.self_symm_id_assoc] using congrArg (fun z => cD ≪≫ z.symm) hD

end Composition

section Identity

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  [EnoughInjectives A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₂} B] [EnoughInjectives B]
  (F : A ⥤ B) (J : B ⥤ B) [F.Additive] [J.Additive] [J.PreservesHomology]

/-- An original right-unit pullback comparison derives to the native derived right
unit after the installed comparison of the original identity functor. -/
theorem rightDerivedFunctorPlusPullbackIso_id
    (σ : F ⋙ J ≅ F) (d : J ≅ 𝟭 B)
    (hc : σ = isoWhiskerLeft F d ≪≫ rightUnitor F) :
    (rightDerivedFunctorPlusCompIsoOfPreservesHomology F J).symm ≪≫
        (F ⋙ J).rightDerivedFunctorPlusIso σ =
      isoWhiskerLeft F.rightDerivedFunctorPlus
          (J.rightDerivedFunctorPlusIso d ≪≫ rightDerivedFunctorPlusIdIso B) ≪≫
        rightUnitor F.rightDerivedFunctorPlus := by
  have hc' : σ.symm ≪≫ isoWhiskerLeft F d ≪≫ rightUnitor F = Iso.refl F := by
    rw [← hc, Iso.symm_self_id]
  have h := rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportRightUnit
    F F J σ.symm d
  rw [hc', rightDerivedFunctorPlusIso_refl, rightDerivedFunctorPlusIso_symm] at h
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc,
    Iso.trans_refl] using
    (congrArg (fun z =>
      (rightDerivedFunctorPlusCompIsoOfPreservesHomology F J).symm ≪≫
        (F ⋙ J).rightDerivedFunctorPlusIso σ ≪≫ z) h).symm

end Identity

end CategoryTheory.Functor
