/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.AffineCharts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.FiniteRealization

/-! # Original chart conjugacy for actual global algebra comparison maps

The two original cartesian chart-object isomorphisms conjugate the actual
relative pullback of the source comparison to Spec of the supplied original
ring-diagram map. Both actual pullback projections and the whole original
structural triangle are retained before any coefficient transport is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

open AffineZariskiSite

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
  {G : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {b : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G} (hb : b.Coequifibered)
  (φ : G ⟶ (toOpensFunctor X).op ⋙ relativeSectionDiagram f)
  (hφ : b ≫ φ = (toOpensFunctor X).op.whiskerLeft (relativeSectionMap f))

/-- The original affine ring map is an actual relative map over the original
Spec chart, with its original structural ring-map equation. -/
def relativeChartMapOver (U : X.AffineZariskiSite) :
    Over.mk (Spec.map (f.app U.1)) ⟶ Over.mk (Spec.map (b.app (op U))) := by
  refine Over.homMk (Spec.map (φ.app (op U))) ?_
  apply (cancel_mono U.2.isoSpec.inv).mp
  exact (Category.assoc (Spec.map (φ.app (op U)))
    (Spec.map (b.app (op U))) U.2.isoSpec.inv).trans
      (relativeAlgebraMap_component_over (relativeSectionMap_coequifibered f) hb φ hφ U)

/-- The original affine-source map, as a relative map over the whole base. -/
def relativeMapFromAffineOver :
    Over.mk f ⟶ Over.mk (relativeGluingData hb).toBase :=
  Over.homMk (relativeMapFromAffine f hb φ) (relativeMapFromAffine_over f hb φ hφ)

/-- The original actual pullback map is exactly the original Spec ring map
under the two original chart-object isomorphisms. -/
@[reassoc]
theorem relativeMapFromAffineOver_pullback_chart (U : X.AffineZariskiSite) :
    (relativeAffineChartObjectIso f U).hom ≫
        (Over.pullback U.2.fromSpec).map (relativeMapFromAffineOver f hb φ hφ) =
      relativeChartMapOver f hb φ hφ U ≫ (relativeGluingChartObjectIso hb U).hom := by
  let d := relativeGluingData hb
  let g := d.toBase
  let j := U.2.fromSpec
  let h := relativeMapFromAffine f hb φ
  let a : Spec Γ(Y, f ⁻¹ᵁ U.1) ⟶ pullback f j :=
    (relativeAffineChartObjectIso f U).hom.left
  let c : Spec (G.obj (op U)) ⟶ pullback g j :=
    (relativeGluingChartObjectIso hb U).hom.left
  let k : pullback f j ⟶ pullback g j :=
    ((Over.pullback j).map (relativeMapFromAffineOver f hb φ hφ)).left
  let r := Spec.map (φ.app (op U))
  let s := Spec.map (f.app U.1)
  let t := Spec.map (b.app (op U))
  let v := (U.2.preimage f).fromSpec
  let w : Spec (G.obj (op U)) ⟶ d.glued := d.cover.f U
  have ha₁ : a ≫ pullback.fst f j = v :=
    (relativeAffineChart_isPullback f U).isoPullback_hom_fst
  have ha₂ : a ≫ pullback.snd f j = s :=
    (relativeAffineChart_isPullback f U).isoPullback_hom_snd
  have hc₁ : c ≫ pullback.fst g j = w :=
    (relativeGluing_affineChart_isPullback hb U).isoPullback_hom_fst
  have hc₂ : c ≫ pullback.snd g j = t :=
    (relativeGluing_affineChart_isPullback hb U).isoPullback_hom_snd
  have hk₁ : k ≫ pullback.fst g j = pullback.fst f j ≫ h :=
    pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd g j = pullback.snd f j :=
    pullback.lift_snd _ _ _
  have hv : v ≫ h = r ≫ w := relativeMapFromAffine_chart f hb φ U
  have hr : r ≫ t = s := Over.w (relativeChartMapOver f hb φ hφ U)
  apply Over.OverMorphism.ext
  change a ≫ k = r ≫ c
  apply pullback.hom_ext
  · have hleft : (a ≫ k) ≫ pullback.fst g j = r ≫ w :=
      (Category.assoc a k (pullback.fst g j)).trans
        ((congrArg (fun q => a ≫ q) hk₁).trans
          ((Category.assoc a (pullback.fst f j) h).symm.trans
            ((congrArg (fun q => q ≫ h) ha₁).trans hv)))
    have hright : (r ≫ c) ≫ pullback.fst g j = r ≫ w :=
      (Category.assoc r c (pullback.fst g j)).trans
        (congrArg (fun q => r ≫ q) hc₁)
    exact hleft.trans hright.symm
  · have hleft : (a ≫ k) ≫ pullback.snd g j = s :=
      (Category.assoc a k (pullback.snd g j)).trans
        ((congrArg (fun q => a ≫ q) hk₂).trans ha₂)
    have hright : (r ≫ c) ≫ pullback.snd g j = s :=
      (Category.assoc r c (pullback.snd g j)).trans
        ((congrArg (fun q => r ≫ q) hc₂).trans hr)
    exact hleft.trans hright.symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
