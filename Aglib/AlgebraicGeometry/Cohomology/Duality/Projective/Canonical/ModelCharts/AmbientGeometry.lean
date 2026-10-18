/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.AtIdeal.Data
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.ModelCharts.TopRestriction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.IsomorphicCharts
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Principal.AmbientIsomorphism.Classes
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal.Coefficient

/-!
# Actual source and differential factors under ambient reparametrization

The actual isomorphism of ambient rings induces the original quotient
isomorphism. The closed square identifies the actual source open with
that quotient map, and the original top-differential restrictions paste.
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
  {A' : CommRingCat.{u}} (eA : C.A ≅ A')

omit [IsClosedImmersion i] in
private theorem ambientRingEquiv_hom :
    eA.commRingCatIsoToRingEquiv.toCommRingCatIso.hom = eA.hom := by
  ext z
  rfl

omit [IsClosedImmersion i] in
/-- The original ambient isomorphism induces the literal quotient map on the ordered list. -/
def canonicalAmbientIsoChartQuotientMap :
    regularListQuotientRing C.regularList ⟶
      regularListQuotientRing (C.regularList.map eA.hom.hom) :=
  (regularListAmbientQuotientEquiv eA.commRingCatIsoToRingEquiv C.regularList).toCommRingCatIso.hom

omit [IsClosedImmersion i] in
instance : IsIso (canonicalAmbientIsoChartQuotientMap C eA) := by
  dsimp only [canonicalAmbientIsoChartQuotientMap]
  infer_instance

omit [IsClosedImmersion i] in
/-- Both literal quotient maps commute with the actual ambient isomorphism. -/
theorem canonicalAmbientIsoChart_ringSquare :
    eA.hom ≫ regularListQuotientMap (C.regularList.map eA.hom.hom) =
      regularListQuotientMap C.regularList ≫ canonicalAmbientIsoChartQuotientMap C eA := by
  ext z
  rfl

omit [IsClosedImmersion i] in
/-- The actual ambient and original quotient isomorphisms form the native Cartesian square. -/
theorem canonicalAmbientIsoChart_isPullback :
    IsPullback (Spec.map (canonicalAmbientIsoChartQuotientMap C eA))
      (Spec.map (regularListQuotientMap (C.regularList.map eA.hom.hom)))
      (Spec.map (regularListQuotientMap C.regularList)) (Spec.map eA.hom) := by
  apply IsPullback.of_horiz_isIso
  constructor
  rw [← Spec.map_comp, ← Spec.map_comp, canonicalAmbientIsoChart_ringSquare]

/-- The original closed square determines the actual quotient-normalized source open. -/
theorem canonicalAmbientIsoChart_source :
    (C.ambientIsoChart eA).quotientSource =
      Spec.map (canonicalAmbientIsoChartQuotientMap C eA) ≫ C.quotientSource := by
  apply (cancel_mono i).mp
  rw [← (C.ambientIsoChart eA).quotientSource_square, Category.assoc,
    ← C.quotientSource_square]
  change Spec.map (regularListQuotientMap (C.regularList.map eA.hom.hom)) ≫
      (Spec.map eA.hom ≫ C.jP) =
    Spec.map (canonicalAmbientIsoChartQuotientMap C eA) ≫
      (Spec.map (regularListQuotientMap C.regularList) ≫ C.jP)
  rw [← Category.assoc, ← Spec.map_comp, canonicalAmbientIsoChart_ringSquare,
    Spec.map_comp, Category.assoc]

omit [IsClosedImmersion i] in
private theorem coefficientNative (c : ℕ) (hc : C.regularList.length = c) :
    canonicalChartCoefficientAtDegree C c hc =
      canonicalTopDifferentialRestrictionInDegree p C.jP (Spec.map C.α) C.jY
        C.ambientSquare.symm n (c + d)
        (C.dimension_eq.trans (congrArg (fun k => k + d) hc)) := rfl

omit [IsClosedImmersion i] in
/-- The original ambient coefficient restriction pastes through the actual rank equality. -/
theorem canonicalAmbientIsoChart_coefficient (c : ℕ) (hc : C.regularList.length = c) :
    (restrictFunctorComp (Spec.map eA.hom) C.jP).hom.app (relativeCanonicalModule p n) ≫
        (restrictFunctor (Spec.map eA.hom)).map (canonicalChartCoefficientAtDegree C c hc).hom ≫
        (canonicalAmbientTopOpenIso C.α eA.hom (c + d)).hom =
      (canonicalChartCoefficientAtDegree (C.ambientIsoChart eA) c
        ((C.ambientIsoChart_regularList_length eA).trans hc)).hom := by
  have hφ : Spec.map eA.hom ≫ Spec.map C.α =
      Spec.map (C.α ≫ eA.hom) ≫ 𝟙 (Spec C.R) := by
    simp only [Spec.map_comp, Category.comp_id]
  have H : (Spec.map eA.hom ≫ C.jP) ≫ p =
      Spec.map (C.α ≫ eA.hom) ≫ (𝟙 (Spec C.R) ≫ C.jY) := by
    rw [Category.assoc, ← C.ambientSquare, ← Category.assoc, ← Spec.map_comp,
      Category.id_comp]
  have hh := canonicalTopDifferentialRestrictionInDegree_comp p (Spec.map C.α)
    (Spec.map (C.α ≫ eA.hom)) C.jP C.jY (Spec.map eA.hom) (𝟙 (Spec C.R))
    C.ambientSquare.symm hφ H n (c + d)
      (C.dimension_eq.trans (congrArg (fun k => k + d) hc))
  simpa only [coefficientNative, SmoothClosedImmersionLocalChart.ambientIsoChart,
    canonicalTopDifferentialRestrictionInDegree, relativeTopDifferentialRestrictionIso,
    canonicalAmbientTopOpenIso, canonicalAmbientDifferentialOpenIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.id_comp, Category.assoc] using hh

/-- The literal original tangent square for an actual ambient reparametrization. -/
def CanonicalAmbientIsoChartTangentSquare : Prop :=
  let s := C.regularList
  let t := s.map eA.hom.hom
  let q' := regularListQuotientMap (A := A') t
  let ψ := canonicalAmbientIsoChartQuotientMap C eA
  let h := canonicalAmbientIsoChart_ringSquare C eA
  let N := moduleExteriorPower X (relativeDifferentialSheaf (i ≫ p)) d
  (restrictFunctorCongr (canonicalAmbientIsoChart_source C eA)).hom.app N ≫
      (restrictFunctorComp (Spec.map ψ) C.quotientSource).hom.app N ≫
      (restrictFunctor (Spec.map ψ)).map
        (canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList s) rfl).hom ≫
      canonicalExteriorOpenMap (Spec.map ψ)
        (relativeDifferentialSheaf (Spec.map (C.α ≫ regularListQuotientMap s)))
        (relativeDifferentialSheaf (Spec.map ((C.α ≫ eA.hom) ≫ q'))) d
        (canonicalAmbientConormalTangentIso C.α eA.hom (regularListQuotientMap s)
          q' ψ h).hom =
    (canonicalChartSourceTopIsoAtIdeal (C.ambientIsoChart eA) (Ideal.ofList t) rfl).hom

/-- The original tangent restriction pastes on the actual ambient-normalized source. -/
theorem canonicalAmbientIsoChart_tangent : CanonicalAmbientIsoChartTangentSquare C eA := by
  unfold CanonicalAmbientIsoChartTangentSquare
  intro s t q' ψ h N
  let a := C.quotientSource
  let a' := (C.ambientIsoChart eA).quotientSource
  have ha : a' = Spec.map ψ ≫ a := canonicalAmbientIsoChart_source C eA
  have hC : a ≫ (i ≫ p) = Spec.map (C.α ≫ regularListQuotientMap s) ≫ C.jY := by
    rw [Spec.map_comp, Category.assoc, C.ambientSquare, ← Category.assoc,
      ← C.quotientSource_square, Category.assoc]
  have hφ := canonicalAmbientSourceSquare C.α eA.hom (regularListQuotientMap s) q' ψ h
  have H : (Spec.map ψ ≫ a) ≫ (i ≫ p) =
      Spec.map ((C.α ≫ eA.hom) ≫ q') ≫ (𝟙 (Spec C.R) ≫ C.jY) := by
    rw [Category.assoc, hC, ← Category.assoc, hφ, Category.assoc]
  have HD : a' ≫ (i ≫ p) =
      Spec.map ((C.α ≫ eA.hom) ≫ q') ≫ (𝟙 (Spec C.R) ≫ C.jY) := by
    rw [ha]
    exact H
  have ht := canonicalTopDifferentialRestriction_comp_congr (i ≫ p)
    (Spec.map (C.α ≫ regularListQuotientMap s))
    (Spec.map ((C.α ≫ eA.hom) ≫ q')) a C.jY (Spec.map ψ) (𝟙 (Spec C.R))
    hC hφ H a' ha HD d
  have hUC : (canonicalChartSourceTopIsoAtIdeal C (Ideal.ofList s) rfl).hom =
      (relativeTopDifferentialRestrictionIso (i ≫ p) a
        (Spec.map (C.α ≫ regularListQuotientMap s)) C.jY hC d).hom := rfl
  have hUD : (canonicalChartSourceTopIsoAtIdeal (C.ambientIsoChart eA)
        (Ideal.ofList t) rfl).hom =
      (relativeTopDifferentialRestrictionIso (i ≫ p) a'
        (Spec.map ((C.α ≫ eA.hom) ≫ q')) C.jY
          (by simpa only [Category.id_comp] using HD) d).hom := rfl
  have hV : canonicalExteriorOpenMap (Spec.map ψ)
        (relativeDifferentialSheaf (Spec.map (C.α ≫ regularListQuotientMap s)))
        (relativeDifferentialSheaf (Spec.map ((C.α ≫ eA.hom) ≫ q'))) d
        (canonicalAmbientConormalTangentIso C.α eA.hom
          (regularListQuotientMap s) q' ψ h).hom =
      (relativeTopDifferentialRestrictionIso
        (Spec.map (C.α ≫ regularListQuotientMap s)) (Spec.map ψ)
        (Spec.map ((C.α ≫ eA.hom) ≫ q')) (𝟙 (Spec C.R)) hφ d).hom := rfl
  rw [hUC, hUD, hV]
  simpa only [a, a', Category.id_comp, Category.assoc] using ht

end AlgebraicGeometry.Scheme.Modules
