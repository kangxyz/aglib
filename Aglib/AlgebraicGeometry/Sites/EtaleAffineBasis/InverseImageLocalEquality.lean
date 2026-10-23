/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.InverseImageLocalRepresentatives
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Local equality of original inverse-image representatives -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)

/-- The presentation of the original inverse image is locally injective. -/
instance inverseImagePresentationMap_isLocallyInjective :
    Presheaf.IsLocallyInjective S.smallEtaleTopology (inverseImagePresentationMap f F) := by
  let : EssentiallySmall.{u + 1} S.Etale := essentiallySmallSelf.{0, u, u + 1} S.Etale
  let : S.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    .ofEssentiallySmall S.smallEtaleTopology
  let e := (Functor.sheafPullbackConstruction.sheafPullbackIso (siteBaseChange f)
    AddCommGrpCat.{u + 1} X.smallEtaleTopology S.smallEtaleTopology).symm.app F
  have : IsIso e.hom.hom :=
    Iso.isIso_hom ((sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso e)
  let h₂ : Presheaf.IsLocallyInjective S.smallEtaleTopology e.hom.hom :=
    inferInstance
  let h₁ : Presheaf.IsLocallyInjective S.smallEtaleTopology
      (toSheafify S.smallEtaleTopology (inverseImagePresentation f F)) :=
    (S.smallEtaleTopology.W_toSheafify (inverseImagePresentation f F)).isLocallyInjective
  exact @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ S.smallEtaleTopology
    _ _ _
    (toSheafify S.smallEtaleTopology (inverseImagePresentation f F)) e.hom.hom h₁ h₂

/-- Equality in the original inverse image is witnessed by finite affine local
equalities in its native Kan presentation. -/
theorem exists_finite_affine_inverseImagePresentation_equal (W : S.Etale)
    [CompactSpace W.left] (s t : (inverseImagePresentation f F).obj (op W))
    (h : (inverseImagePresentationMap f F).app (op W) s =
      (inverseImagePresentationMap f F).app (op W) t) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.Etale) (g : ∀ i, V i ⟶ W),
      (∀ i, IsAffine (V i).left) ∧
      (Sieve.ofArrows V g ∈ S.smallEtaleTopology W) ∧
      ∀ i, (inverseImagePresentation f F).map (g i).op s =
        (inverseImagePresentation f F).map (g i).op t := by
  obtain ⟨ι, hι, V, g, hV, hg, hcover⟩ := exists_finite_affine_family W
    (Presheaf.equalizerSieve s t)
    (Presheaf.equalizerSieve_mem S.smallEtaleTopology (inverseImagePresentationMap f F) s t h)
  exact ⟨ι, hι, V, g, hV, hcover, hg⟩

/-- Equality of two original-section representatives in the Kan extension is
witnessed by actual restrictions on a common original etale object. -/
theorem exists_common_inverseImagePresentation_representative (W : S.Etale)
    (U V : X.Etale) (a : W ⟶ (siteBaseChange f).obj U)
    (b : W ⟶ (siteBaseChange f).obj V) (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (h : (inverseImagePresentation f F).map a.op
        (((siteBaseChange f).op.lanUnit.app F.obj).app (op U) s) =
      (inverseImagePresentation f F).map b.op
        (((siteBaseChange f).op.lanUnit.app F.obj).app (op V) t)) :
    ∃ (T : X.Etale) (c : W ⟶ (siteBaseChange f).obj T) (p : T ⟶ U) (q : T ⟶ V),
      c ≫ (siteBaseChange f).map p = a ∧
      c ≫ (siteBaseChange f).map q = b ∧ F.obj.map p.op s = F.obj.map q.op t := by
  let G := siteBaseChange f
  let : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  let : IsFiltered (CostructuredArrow G.op (op W)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence G W)
  let : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let hc := Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op F.obj (op W)
  obtain ⟨T, p, q, hpq⟩ := (Types.FilteredColimit.isColimit_eq_iff _
    (isColimitOfPreserves (CategoryTheory.forget AddCommGrpCat.{u + 1}) hc)
    (i := CostructuredArrow.mk a.op) (j := CostructuredArrow.mk b.op)
    (xi := s) (xj := t)).mp h
  refine ⟨T.left.unop, T.hom.unop, p.left.unop, q.left.unop, ?_, ?_, hpq⟩
  · exact congrArg Quiver.Hom.unop (CostructuredArrow.w p)
  · exact congrArg Quiver.Hom.unop (CostructuredArrow.w q)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
