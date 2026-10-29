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
  let g := (relativeGluingData hb).toBase
  let j := U.2.fromSpec
  let h := relativeMapFromAffine f hb φ
  let a : Spec Γ(Y, f ⁻¹ᵁ U.1) ⟶ pullback f j :=
    (relativeAffineChartObjectIso f U).hom.left
  let c : Spec (G.obj (op U)) ⟶ pullback g j :=
    (relativeGluingChartObjectIso hb U).hom.left
  let k : pullback f j ⟶ pullback g j :=
    ((Over.pullback j).map (relativeMapFromAffineOver f hb φ hφ)).left
  let r := Spec.map (φ.app (op U))
  have ha₁ : a ≫ pullback.fst f j = (U.2.preimage f).fromSpec :=
    (relativeAffineChart_isPullback f U).isoPullback_hom_fst
  have ha₂ : a ≫ pullback.snd f j = Spec.map (f.app U.1) :=
    (relativeAffineChart_isPullback f U).isoPullback_hom_snd
  have hc₁ : c ≫ pullback.fst g j = (relativeGluingData hb).cover.f U :=
    (relativeGluing_affineChart_isPullback hb U).isoPullback_hom_fst
  have hc₂ : c ≫ pullback.snd g j = Spec.map (b.app (op U)) :=
    (relativeGluing_affineChart_isPullback hb U).isoPullback_hom_snd
  have hk₁ : k ≫ pullback.fst g j = pullback.fst f j ≫ h :=
    pullback.lift_fst _ _ _
  have hk₂ : k ≫ pullback.snd g j = pullback.snd f j :=
    pullback.lift_snd _ _ _
  apply Over.OverMorphism.ext
  change a ≫ k = r ≫ c
  apply pullback.hom_ext
  · change (a ≫ k) ≫ pullback.fst g j = (r ≫ c) ≫ pullback.fst g j
    rw [Category.assoc a k (pullback.fst g j), hk₁,
      ← Category.assoc a (pullback.fst f j) h, ha₁,
      Category.assoc r c (pullback.fst g j), hc₁]
    exact relativeMapFromAffine_chart f hb φ U
  · change (a ≫ k) ≫ pullback.snd g j = (r ≫ c) ≫ pullback.snd g j
    rw [Category.assoc a k (pullback.snd g j), hk₂,
      Category.assoc r c (pullback.snd g j), hc₂]
    exact ha₂.trans (Over.w (relativeChartMapOver f hb φ hφ U)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
