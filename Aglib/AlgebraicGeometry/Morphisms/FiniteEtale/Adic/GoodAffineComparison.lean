/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.GoodAffineGluing
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalOpenCoverColimits

/-!
# Original local comparisons for a glued affine algebra cover

This comparison uses the original inverse-image open cover and the native
base-change preservation of its over-category colimit. The concrete adic
consumer supplies the local maps from its original quotient units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteEtale.AffineAlgebraGluing

universe u
open PurelyInseparable.Global

/-- Naturality of Cartesian comparison maps, proved on the entire abstract
map-and-square packet before any original gluing diagram is substituted. -/
theorem pullbackComparison_naturality
    {W₀ W₁ Z₀ Z₁ T X : Scheme.{u}} {i : T ⟶ X}
    {a₀ : W₀ ⟶ Z₀} {a₁ : W₁ ⟶ Z₁} {b₀ : W₀ ⟶ T} {b₁ : W₁ ⟶ T}
    {f₀ : Z₀ ⟶ X} {f₁ : Z₁ ⟶ X}
    (H₀ : IsPullback a₀ b₀ f₀ i) (H₁ : IsPullback a₁ b₁ f₁ i)
    (s : W₀ ⟶ W₁) (t : Z₀ ⟶ Z₁) (ht : t ≫ f₁ = f₀)
    (ha : s ≫ a₁ = a₀ ≫ t) (hb : s ≫ b₁ = b₀) :
    s ≫ H₁.isoPullback.hom = H₀.isoPullback.hom ≫
      ((Over.pullback i).map (Over.homMk t ht : Over.mk f₀ ⟶ Over.mk f₁)).left := by
  apply pullback.hom_ext
  · change (s ≫ H₁.isoPullback.hom) ≫ pullback.fst _ _ =
      (H₀.isoPullback.hom ≫ pullback.lift (pullback.fst _ _ ≫ t)
        (pullback.snd _ _) _) ≫ pullback.fst _ _
    rw [Category.assoc, H₁.isoPullback_hom_fst, Category.assoc,
      pullback.lift_fst, ← Category.assoc, H₀.isoPullback_hom_fst]
    exact ha
  · change (s ≫ H₁.isoPullback.hom) ≫ pullback.snd _ _ =
      (H₀.isoPullback.hom ≫ pullback.lift (pullback.fst _ _ ≫ t)
        (pullback.snd _ _) _) ≫ pullback.snd _ _
    rw [Category.assoc, H₁.isoPullback_hom_snd, Category.assoc,
      pullback.lift_snd, H₀.isoPullback_hom_snd]
    exact hb

variable {X : Scheme.{u}} (F : X.Opensᵒᵖ ⥤ CommRingCat.{u}) (η : X.presheaf ⟶ F)
  (hcart : ∀ (U V : X.Opens) (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (h : U ≤ V), IsPullback (Spec.map (F.map (homOfLE h).op))
      (Spec.map (η.app (op U))) (Spec.map (η.app (op V)))
      (Spec.map (X.presheaf.map (homOfLE h).op)))
  (hcover : ∀ x : X, ∃ U, IsGood F η U ∧ x ∈ U)
  {Y : Scheme.{u}} (p : Y ⟶ X)

/-- The original inverse images of the good affine opens. -/
def goodInverseImageCover : Y.OpenCover :=
  Y.openCoverOfIsOpenCover (fun U : GoodOpen F η => p ⁻¹ᵁ U.val) (by
    apply p.iSup_preimage_eq_top
    apply top_unique
    intro x _
    obtain ⟨U, hU, hxU, _⟩ := Opens.isBasis_iff_nbhd.mp
      (goodOpen_isBasis F η hcart hcover) (Opens.mem_top x)
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩)

/-- The inverse-image cover inherits the inclusion order of the original good opens. -/
instance instPreorderGoodInverseImageCover :
    Preorder (goodInverseImageCover F η hcart hcover p).I₀ :=
  inferInstanceAs (Preorder (GoodOpen F η))

/-- Directedness is inherited from refinement on the original base, without
asserting that inverse images form a basis of the source. -/
instance instLocallyDirectedGoodInverseImageCover :
    (goodInverseImageCover F η hcart hcover p).LocallyDirected where
  trans {U V} i := Y.homOfLE (p.preimage_mono i.le)
  trans_id U := by apply Scheme.homOfLE_rfl
  trans_comp i j := (Scheme.homOfLE_homOfLE _ _ _).symm
  w i := Scheme.homOfLE_ι _ _
  directed {U V} x := by
    change (pullback (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι).carrier at x
    let y := pullback.fst (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι x
    have hxV : p y.val ∈ V.val := by
      have h := congrArg (fun k : pullback (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι ⟶ Y => k x)
        (pullback.condition (f := (p ⁻¹ᵁ U.val).ι) (g := (p ⁻¹ᵁ V.val).ι))
      change y.val = (pullback.snd (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι x).val at h
      rw [h]
      exact (pullback.snd (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι x).property
    obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp
      (goodOpen_isBasis F η hcart hcover)
      (show p y.val ∈ U.val ⊓ V.val from ⟨y.property, hxV⟩)
    refine ⟨⟨W, hW⟩, homOfLE (hWUV.trans inf_le_left),
      homOfLE (hWUV.trans inf_le_right), ⟨y.val, hxW⟩, ?_⟩
    apply (pullback.fst (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι ≫
      (p ⁻¹ᵁ U.val).ι).isOpenEmbedding.injective
    change ((pullback.lift
      (Y.homOfLE (p.preimage_mono (hWUV.trans inf_le_left)))
      (Y.homOfLE (p.preimage_mono (hWUV.trans inf_le_right))) _ ≫
      pullback.fst (p ⁻¹ᵁ U.val).ι (p ⁻¹ᵁ V.val).ι ≫ (p ⁻¹ᵁ U.val).ι)
        ⟨y.val, hxW⟩) = y.val
    rw [pullback.lift_fst_assoc, Scheme.homOfLE_ι]
    rfl
  property_trans i := inferInstance

variable (hfinite : ∀ (U : X.Opens), IsAffineOpen U → (η.app (op U)).hom.Finite)
  {T : Scheme.{u}} (i : T ⟶ X) (Z : Over T)
  (a : ∀ U : GoodOpen F η, ((Z.hom ≫ i) ⁻¹ᵁ U.val).toScheme ⟶
    Spec (F.obj (op U.val)))
  (ha : ∀ {U V : GoodOpen F η} (j : U ⟶ V),
    Z.left.homOfLE ((Z.hom ≫ i).preimage_mono j.le) ≫ a V =
      a U ≫ Spec.map (F.map (homOfLE (show U.val ≤ V.val from j.le)).op))
  (hrect : ∀ U : GoodOpen F η, IsPullback (a U)
    (((Z.hom ≫ i) ⁻¹ᵁ U.val).ι ≫ Z.hom)
    ((datum F η hcart hcover).cover.f U ≫
      (cover F η hcart hcover hfinite).obj.hom) i)

/-- Original local Cartesian maps give the actual isomorphism of the two
open-cover diagrams after base change. -/
def originalComparisonDiagramIso :
    overCoverDiagram Z (goodInverseImageCover F η hcart hcover (Z.hom ≫ i)) ≅
      overCoverDiagram (cover F η hcart hcover hfinite).obj
        (datum F η hcart hcover).cover ⋙ Over.pullback i :=
  NatIso.ofComponents
    (fun U => Over.isoMk (hrect U).isoPullback (hrect U).isoPullback_hom_snd) (by
      intro U V j
      change GoodOpen F η at U V
      apply Over.OverMorphism.ext
      refine pullbackComparison_naturality (hrect U) (hrect V)
        ((goodInverseImageCover F η hcart hcover (Z.hom ≫ i)).trans j)
        ((datum F η hcart hcover).cover.trans j)
        (Over.w ((overCoverDiagram (cover F η hcart hcover hfinite).obj
          (datum F η hcart hcover).cover).map j)) (ha j) ?_
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ Z.hom)
          ((goodInverseImageCover F η hcart hcover (Z.hom ≫ i)).trans_map j)))

/-- The specified global comparison is the native comparison of colimit
points of the original local diagram isomorphism. -/
def originalComparisonIso :
    (Over.pullback i).obj (cover F η hcart hcover hfinite).obj ≅ Z :=
  (pullbackOverCoverCoconeIsColimit (cover F η hcart hcover hfinite).obj
    (datum F η hcart hcover).cover i).coconePointsIsoOfNatIso
      (overCoverCoconeIsColimit Z
        (goodInverseImageCover F η hcart hcover (Z.hom ≫ i)))
      (originalComparisonDiagramIso F η hcart hcover hfinite i Z a ha hrect).symm

end AlgebraicGeometry.Scheme.FiniteEtale.AffineAlgebraGluing
