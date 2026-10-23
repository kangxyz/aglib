/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.InverseImageUnit
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.InverseImageLocalEquality

/-! # Original-unit local descriptions of inverse-image sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)

/-- A native presentation representative maps to restriction of the original
inverse-image adjunction unit. -/
lemma inverseImagePresentationMap_representative (W : S.Etale) (U : X.Etale)
    (a : W ⟶ (siteBaseChange f).obj U) (t : F.obj.obj (op U)) :
    (inverseImagePresentationMap f F).app (op W)
        ((inverseImagePresentation f F).map a.op
          (((siteBaseChange f).op.lanUnit.app F.obj).app (op U) t)) =
      ((inverseImage f).obj F).obj.map a.op
        (((inverseImageAdjunction f).unit.app F).hom.app (op U) t) := by
  exact (NatTrans.naturality_apply (inverseImagePresentationMap f F) a.op
    (((siteBaseChange f).op.lanUnit.app F.obj).app (op U) t)).trans
    (congrArg (((inverseImage f).obj F).obj.map a.op)
      (ConcreteCategory.congr_hom (inverseImagePresentationMap_unit f F U) t))

/-- Finite affine local representatives expressed entirely through the original
inverse-image adjunction, with no presentation replacement in the conclusion. -/
theorem exists_finite_affine_inverseImage_unit_representatives (W : S.Etale)
    [CompactSpace W.left] (s : ((inverseImage f).obj F).obj.obj (op W)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → S.Etale) (g : ∀ i, V i ⟶ W),
      (∀ i, IsAffine (V i).left) ∧
      (Sieve.ofArrows V g ∈ S.smallEtaleTopology W) ∧
      ∀ i, ∃ (U : X.Etale) (a : V i ⟶ (siteBaseChange f).obj U)
        (t : F.obj.obj (op U)),
        ((inverseImage f).obj F).obj.map a.op
          (((inverseImageAdjunction f).unit.app F).hom.app (op U) t) =
          ((inverseImage f).obj F).obj.map (g i).op s := by
  obtain ⟨ι, hι, V, g, hV, hg, hs⟩ :=
    exists_finite_affine_inverseImage_representatives f F W s
  refine ⟨ι, hι, V, g, hV, hg, fun i ↦ ?_⟩
  obtain ⟨U, a, t, ht⟩ := hs i
  exact ⟨U, a, t, (inverseImagePresentationMap_representative f F (V i) U a t).symm.trans ht⟩


/-- Equality of original-unit local sections is witnessed on a finite affine
cover by a common original etale object and equality in the original sheaf. -/
theorem exists_finite_affine_inverseImage_unit_equality (W : S.Etale)
    [CompactSpace W.left] (U V : X.Etale)
    (a : W ⟶ (siteBaseChange f).obj U) (b : W ⟶ (siteBaseChange f).obj V)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (h : ((inverseImage f).obj F).obj.map a.op
        (((inverseImageAdjunction f).unit.app F).hom.app (op U) s) =
      ((inverseImage f).obj F).obj.map b.op
        (((inverseImageAdjunction f).unit.app F).hom.app (op V) t)) :
    ∃ (ι : Type u) (_ : Finite ι) (Z : ι → S.Etale) (g : ∀ i, Z i ⟶ W),
      (∀ i, IsAffine (Z i).left) ∧
      (Sieve.ofArrows Z g ∈ S.smallEtaleTopology W) ∧
      ∀ i, ∃ (T : X.Etale) (c : Z i ⟶ (siteBaseChange f).obj T)
        (p : T ⟶ U) (q : T ⟶ V),
        c ≫ (siteBaseChange f).map p = g i ≫ a ∧
        c ≫ (siteBaseChange f).map q = g i ≫ b ∧
        F.obj.map p.op s = F.obj.map q.op t := by
  let P := inverseImagePresentation f F
  let s' := P.map a.op (((siteBaseChange f).op.lanUnit.app F.obj).app (op U) s)
  let t' := P.map b.op (((siteBaseChange f).op.lanUnit.app F.obj).app (op V) t)
  have h' : (inverseImagePresentationMap f F).app (op W) s' =
      (inverseImagePresentationMap f F).app (op W) t' := by
    exact (inverseImagePresentationMap_representative f F W U a s).trans
      (h.trans (inverseImagePresentationMap_representative f F W V b t).symm)
  obtain ⟨ι, hι, Z, g, hZ, hg, heq⟩ :=
    exists_finite_affine_inverseImagePresentation_equal f F W s' t' h'
  refine ⟨ι, hι, Z, g, hZ, hg, fun i ↦ ?_⟩
  apply exists_common_inverseImagePresentation_representative f F (Z i)
    U V (g i ≫ a) (g i ≫ b) s t
  let s₀ : P.obj (op ((siteBaseChange f).obj U)) :=
    ((siteBaseChange f).op.lanUnit.app F.obj).app (op U) s
  let t₀ : P.obj (op ((siteBaseChange f).obj V)) :=
    ((siteBaseChange f).op.lanUnit.app F.obj).app (op V) t
  have ha : P.map (g i ≫ a).op s₀ = P.map (g i).op (P.map a.op s₀) :=
    ConcreteCategory.congr_hom (P.map_comp a.op (g i).op) s₀
  have hb : P.map (g i ≫ b).op t₀ = P.map (g i).op (P.map b.op t₀) :=
    ConcreteCategory.congr_hom (P.map_comp b.op (g i).op) t₀
  exact ha.trans ((heq i).trans hb.symm)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
