/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactTriangleIdentity
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactTriangleComposition

/-! # Original localized isomorphisms and structural composition coherence -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
universe uA vA wA uB vB wB uC vC wC uD vD wD
section Iso
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  (F G H : A ⥤ B) [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- Localization retains the inverse of the original isomorphism. -/
theorem mapDerivedCategoryOriginalIso_symm (e : F ≅ G) :
    mapDerivedCategoryOriginalIso G F e.symm =
      (mapDerivedCategoryOriginalIso F G e).symm := rfl

/-- Localization retains composition of the original isomorphisms. -/
theorem mapDerivedCategoryOriginalIso_trans (e : F ≅ G) (d : G ≅ H) :
    mapDerivedCategoryOriginalIso F H (e ≪≫ d) =
      mapDerivedCategoryOriginalIso F G e ≪≫ mapDerivedCategoryOriginalIso G H d := by
  apply Iso.ext
  simp only [mapDerivedCategoryOriginalIso, Localization.liftNatIso_hom, Iso.trans_hom,
    isoWhiskerRight_hom, NatIso.mapHomologicalComplex, Localization.comp_liftNatTrans,
    ← whiskerRight_comp, ← NatTrans.mapHomologicalComplex_comp]

/-- Localization of a literal original functor equality is the same equality transport. -/
theorem mapDerivedCategoryOriginalIso_eqToIso (e : F = G) :
    mapDerivedCategoryOriginalIso F G (eqToIso e) =
      eqToIso (by cases e; rfl : F.mapDerivedCategory = G.mapDerivedCategory) := by
  subst G
  apply Iso.ext
  simp only [mapDerivedCategoryOriginalIso, eqToIso_refl, Iso.refl_hom,
    Localization.liftNatIso_hom, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex_id, isoWhiskerRight_hom, whiskerRight_id',
    Localization.liftNatTrans_id]
end Iso

section Associativity
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D)
  (M : A ⥤ C) (N : B ⥤ D) (P : A ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [M.Additive] [N.Additive] [P.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits M] [PreservesFiniteColimits M]
  [PreservesFiniteLimits N] [PreservesFiniteColimits N]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- Original coherent compositors retain their exact unbounded associativity equation. -/
theorem mapDerivedCategoryCompositeIso_assoc
    (ef : M ≅ F ⋙ G) (ek : P ≅ M ⋙ H) (et : P ≅ F ⋙ N) (c : N ≅ G ⋙ H)
    (hc : et ≪≫ isoWhiskerLeft F c =
      ek ≪≫ isoWhiskerRight ef H ≪≫ associator F G H) :
    mapDerivedCategoryCompositeIso F N P et ≪≫
        isoWhiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompositeIso G H N c) =
      mapDerivedCategoryCompositeIso M H P ek ≪≫
        isoWhiskerRight (mapDerivedCategoryCompositeIso F G M ef) H.mapDerivedCategory ≪≫
        associator F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory := by
  have ht : et.symm = isoWhiskerLeft F c ≪≫ (associator F G H).symm ≪≫
      isoWhiskerRight ef.symm H ≪≫ ek.symm := by
    have hh := congrArg (fun z => et.symm ≪≫ z ≪≫ (associator F G H).symm ≪≫
      (isoWhiskerRight ef H).symm ≪≫ ek.symm) hc
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc,
      Iso.self_symm_id, Iso.trans_refl, ← isoWhiskerRight_symm] using hh.symm
  have hh := mapDerivedCategoryTriangleIso_comp F G H M N P ef.symm ek.symm et.symm c ht
  simp only [mapDerivedCategoryTriangleIso, mapDerivedCategoryOriginalIso_symm] at hh
  change (mapDerivedCategoryCompositeIso F N P et).symm =
      isoWhiskerLeft F.mapDerivedCategory (mapDerivedCategoryCompositeIso G H N c) ≪≫
        (associator F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory).symm ≪≫
        (isoWhiskerRight (mapDerivedCategoryCompositeIso F G M ef)
          H.mapDerivedCategory).symm ≪≫
        (mapDerivedCategoryCompositeIso M H P ek).symm at hh
  have hh' := congrArg (fun z => mapDerivedCategoryCompositeIso F N P et ≪≫ z ≪≫
    mapDerivedCategoryCompositeIso M H P ek ≪≫
      isoWhiskerRight (mapDerivedCategoryCompositeIso F G M ef) H.mapDerivedCategory ≪≫
      associator F.mapDerivedCategory G.mapDerivedCategory H.mapDerivedCategory) hh
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id_assoc,
    Iso.symm_self_id, Iso.trans_refl] using hh'.symm
end Associativity
end CategoryTheory.Functor
