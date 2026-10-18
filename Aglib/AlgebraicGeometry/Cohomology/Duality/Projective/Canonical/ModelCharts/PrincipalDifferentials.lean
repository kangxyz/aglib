/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AtIdeal.Data
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.TopRestriction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.PrincipalGeometry
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal.Coefficient

/-!
# Original differential factors on actual principal chart refinements

The original ambient coefficient and source tangent isomorphisms paste
along the actual principal source. The original restriction composition
and source congruence remain visible, including the genuine ambient rank.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Cohomology

universe u
namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ}
  [IsClosedImmersion i] {x : X} (C : SmoothClosedImmersionLocalChart i p n d x)
  (r : C.A) (hr : C.σ r ∉ C.point.asIdeal)

omit [IsClosedImmersion i] in
/-- The original localized list retains the same genuine normal degree. -/
theorem canonicalPrincipalChart_length (c : ℕ) (hc : C.regularList.length = c) :
    (C.principalChart r hr).regularList.length = c :=
  (List.length_map (as := C.regularList) (algebraMap C.A (Localization.Away r))).trans hc

omit [IsClosedImmersion i] in
private theorem coefficientNative (c : ℕ) (hc : C.regularList.length = c) :
    canonicalChartCoefficientAtDegree C c hc =
      canonicalTopDifferentialRestrictionInDegree p C.jP (Spec.map C.α) C.jY
        C.ambientSquare.symm n (c + d)
        (C.dimension_eq.trans (congrArg (fun k => k + d) hc)) := by
  rfl

omit [IsClosedImmersion i] in
/-- Original ambient top restriction pastes through the same actual rank equality. -/
theorem canonicalPrincipalChart_coefficient (c : ℕ) (hc : C.regularList.length = c) :
    let φ : C.A ⟶ CommRingCat.of (Localization.Away r) :=
      CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let D := C.principalChart r hr
    (restrictFunctorComp (Spec.map φ) C.jP).hom.app (relativeCanonicalModule p n) ≫
      (restrictFunctor (Spec.map φ)).map (canonicalChartCoefficientAtDegree C c hc).hom ≫
      (canonicalAmbientTopOpenIso C.α φ (c + d)).hom =
    (canonicalChartCoefficientAtDegree D c (canonicalPrincipalChart_length C r hr c hc)).hom := by
  intro φ D
  have hφ : Spec.map φ ≫ Spec.map C.α = Spec.map (C.α ≫ φ) ≫ 𝟙 (Spec C.R) := by
    simp only [Spec.map_comp, Category.comp_id]
  have H : (Spec.map φ ≫ C.jP) ≫ p = Spec.map (C.α ≫ φ) ≫ (𝟙 (Spec C.R) ≫ C.jY) := by
    rw [Category.assoc, ← C.ambientSquare, ← Category.assoc, ← Spec.map_comp,
      Category.id_comp]
  have hnm : n = c + d :=
    C.quotientChart.dimension_eq.trans (congrArg (fun k => k + d) hc)
  have h := canonicalTopDifferentialRestrictionInDegree_comp p (Spec.map C.α)
    (Spec.map (C.α ≫ φ)) C.jP C.jY (Spec.map φ) (𝟙 (Spec C.R))
    C.ambientSquare.symm hφ H n (c + d) hnm
  simpa only [coefficientNative, D, SmoothClosedImmersionLocalChart.principalChart,
    canonicalTopDifferentialRestrictionInDegree, relativeTopDifferentialRestrictionIso,
    canonicalAmbientTopOpenIso, canonicalAmbientDifferentialOpenIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.id_comp, Category.assoc] using h

omit [IsClosedImmersion i] in
private theorem principalAlpha : (C.principalChart r hr).α =
    C.α ≫ (CommRingCat.ofHom (algebraMap C.A (Localization.Away r)) :
      C.A ⟶ CommRingCat.of (Localization.Away r)) := rfl

omit [IsClosedImmersion i] in
private theorem principalList : (C.principalChart r hr).regularList =
    regularListPrincipalList C.regularList r := rfl

omit [IsClosedImmersion i] in
private theorem principalBaseOpen : (C.principalChart r hr).jY = C.jY := rfl

/-- The original tangent determinant pastes on the actual equal principal source,
with its original restriction congruence and composition arrows. -/
def CanonicalPrincipalChartTangentSquare : Prop :=
    let φ : C.A ⟶ CommRingCat.of (Localization.Away r) :=
      CommRingCat.ofHom (algebraMap C.A (Localization.Away r))
    let s := C.regularList
    let t : List (CommRingCat.of (Localization.Away r)) := regularListPrincipalList s r
    let q' := regularListQuotientMap (A := CommRingCat.of (Localization.Away r)) t
    let ψ := regularListPrincipalLiteralQuotientMap s r
    let h := regularListPrincipalLiteralQuotientMap_square s r
    let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
    (restrictFunctorCongr (canonicalPrincipalChart_source C r hr)).hom.app N ≫
      (restrictFunctorComp (Spec.map ψ) C.quotientChart.jX).hom.app N ≫
      (restrictFunctor (Spec.map ψ)).map
        (canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList s) rfl).hom ≫
      canonicalExteriorOpenMap (Spec.map ψ)
        (relativeDifferentialSheaf (Spec.map (C.α ≫ regularListQuotientMap s)))
        (relativeDifferentialSheaf (Spec.map ((C.α ≫ φ) ≫ q'))) d
        (canonicalAmbientConormalTangentIso C.α φ (regularListQuotientMap s)
          (q') ψ h).hom =
    (canonicalChartSourceTopIsoAtIdeal (C.principalChart r hr) (Ideal.ofList t) rfl).hom

/-- The actual original tangent determinants paste on the native equal principal source. -/
theorem canonicalPrincipalChart_tangent : CanonicalPrincipalChartTangentSquare C r hr := by
  unfold CanonicalPrincipalChartTangentSquare
  intro φ s t q' ψ h N
  let a := C.quotientSource
  let a' := (C.principalChart r hr).quotientSource
  have ha : a' = Spec.map ψ ≫ a := by
    simpa only [a, a', canonicalChartQuotientSource_eq] using
      canonicalPrincipalChart_source C r hr
  have hC : a ≫ (i ≫ p) = Spec.map (C.α ≫ regularListQuotientMap s) ≫ C.jY := by
    rw [Spec.map_comp, Category.assoc, C.ambientSquare, ← Category.assoc,
      ← C.quotientSource_square, Category.assoc]
  have hφ := canonicalAmbientSourceSquare C.α φ (regularListQuotientMap s)
    (q') ψ h
  have H : (Spec.map ψ ≫ a) ≫ (i ≫ p) =
      Spec.map ((C.α ≫ φ) ≫ q') ≫ (𝟙 (Spec C.R) ≫ C.jY) := by
    rw [Category.assoc, hC, ← Category.assoc, hφ, Category.assoc]
  have HD : a' ≫ (i ≫ p) =
      Spec.map ((C.α ≫ φ) ≫ q') ≫ (𝟙 (Spec C.R) ≫ C.jY) := by
    rw [ha]
    exact H
  have ht := canonicalTopDifferentialRestriction_comp_congr (i ≫ p)
    (Spec.map (C.α ≫ regularListQuotientMap s))
    (Spec.map ((C.α ≫ φ) ≫ q')) a C.jY
    (Spec.map ψ) (𝟙 (Spec C.R)) hC hφ H a' ha HD d
  have hUC : (canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList s) rfl).hom =
      (relativeTopDifferentialRestrictionIso (i ≫ p) a
        (Spec.map (C.α ≫ regularListQuotientMap s)) C.jY hC d).hom := rfl
  have hUD : (canonicalChartSourceTopIsoAtIdeal (C.principalChart r hr)
        (Ideal.ofList t) rfl).hom =
      (relativeTopDifferentialRestrictionIso (i ≫ p) a'
        (Spec.map ((C.α ≫ φ) ≫ q')) C.jY
          (by simpa only [Category.id_comp] using HD) d).hom := rfl
  have hV : canonicalExteriorOpenMap (Spec.map ψ)
        (relativeDifferentialSheaf (Spec.map (C.α ≫ regularListQuotientMap s)))
        (relativeDifferentialSheaf (Spec.map ((C.α ≫ φ) ≫ q'))) d
        (canonicalAmbientConormalTangentIso C.α φ (regularListQuotientMap s) q' ψ h).hom =
      (relativeTopDifferentialRestrictionIso
        (Spec.map (C.α ≫ regularListQuotientMap s)) (Spec.map ψ)
        (Spec.map ((C.α ≫ φ) ≫ q')) (𝟙 (Spec C.R)) hφ d).hom := rfl
  rw [hUC, hUD, hV]
  simpa only [a, a', canonicalChartQuotientSource_eq, Category.id_comp,
    Category.assoc] using ht

end AlgebraicGeometry.Scheme.Modules
