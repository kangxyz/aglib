/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedCoherentQuotient
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedComparisonRestriction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedPushforwardQuotientRestriction
public import Aglib.AlgebraicGeometry.Modules.InternalHom.GluingIsomorphisms
public import Aglib.AlgebraicGeometry.Modules.Restriction.OverlapFamilyComparison
public import Aglib.AlgebraicGeometry.AffineScheme.OpenChartIntersection

/-! # Coherent geometric realization of the original formal graded coefficient

The coefficient is the actual quotient obtained by coherent relation-kernel
gluing. Its original affine section comparisons glue to an isomorphism of
its actual direct image with the original coproduct of formal graded pieces.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent
namespace AlgebraicGeometry.Scheme.Cohomology
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  [X.IsSeparated] (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))
  {ι : Type u} (U : ι → X.affineOpens) (hU : ∀ x : X, ∃ i, x ∈ (U i).val)
  (P : (formalGradedSpace f I).Modules) (q : formalGradedAmbient f I F ⟶ P) [Epi q]
  (e : ∀ i, P.restrict (formalGradedChart f I (U i)) ≅
    tilde (formalGradedLocalModule f I F (U i)))
  (he : ∀ i, (Scheme.Modules.restrictFunctor (formalGradedChart f I (U i))).map q ≫ (e i).hom =
    formalGradedLocalQuotient f I F (U i))

include q he in
/-- Original quotient equations force compatibility of the local direct-image
comparisons on the original base cover. -/
private theorem formalGradedPushforwardChartsCompatibilityProof :
    InternalHom.RestrictionHomCompatible (fun i => (U i).property.fromSpec)
      ((Scheme.Modules.pushforward (formalGradedProjection f I)).obj P) F.gradedUnderlying
      (fun i => (formalGradedPushforwardChartIso f I F (U i) P (e i)).hom) :=
  let W (i k : ι) : X.affineOpens :=
    ⟨(U i).val ⊓ (U k).val, (U i).property.inf (U k).property⟩
  let a (i k : ι) := Spec.map (X.presheaf.map
    (homOfLE (show (W i k).val ≤ (U i).val from inf_le_left)).op)
  let b (i k : ι) := Spec.map (X.presheaf.map
    (homOfLE (show (W i k).val ≤ (U k).val from inf_le_right)).op)
  let c (i k : ι) := (W i k).property.fromSpec
  have ha (i k : ι) : a i k ≫ (U i).property.fromSpec = c i k :=
    (U i).property.map_fromSpec (W i k).property (homOfLE inf_le_left).op
  have hb (i k : ι) : b i k ≫ (U k).property.fromSpec = c i k :=
    (U k).property.map_fromSpec (W i k).property (homOfLE inf_le_right).op
  letI (i k : ι) : IsOpenImmersion (a i k) := by
    have : IsOpenImmersion (a i k ≫ (U i).property.fromSpec) := by
      rw [ha i k]
      infer_instance
    exact IsOpenImmersion.of_comp _ (U i).property.fromSpec
  letI (i k : ι) : IsOpenImmersion (b i k) := by
    have : IsOpenImmersion (b i k ≫ (U k).property.fromSpec) := by
      rw [hb i k]
      infer_instance
    exact IsOpenImmersion.of_comp _ (U k).property.fromSpec
  let eW (i k : ι) :=
    formalGradedComparisonRestriction f I F (U i) (W i k) inf_le_left P (e i)
  have hi (i k : ι) := formalGradedPushforwardChartIso_restriction_of_quotients f I F
    (U i) (W i k) inf_le_left P (e i) (eW i k) q (he i)
    (formalGradedComparisonRestriction_quotient f I F
      (U i) (W i k) inf_le_left P (e i) q (he i))
  have hk (i k : ι) := formalGradedPushforwardChartIso_restriction_of_quotients f I F
    (U k) (W i k) inf_le_right P (e k) (eW i k) q (he k)
    (formalGradedComparisonRestriction_quotient f I F
      (U i) (W i k) inf_le_left P (e i) q (he i))
  restrictionHomCompatible_of_refinements
    (fun i => (U i).property.fromSpec) (fun i k => Spec Γ(X, W i k)) a b c
    (fun i k => affineOpenIntersection_isPullback
      (U i) (U k) (W i k) inf_le_left inf_le_right rfl) ha hb
    ((Scheme.Modules.pushforward (formalGradedProjection f I)).obj P) F.gradedUnderlying
    (fun i => (formalGradedPushforwardChartIso f I F (U i) P (e i)).hom)
    (fun i k => (formalGradedPushforwardChartIso f I F (W i k) P (eW i k)).hom)
    hi hk

include q he in
/-- The original local pushforward comparisons agree on every actual overlap. -/
theorem formalGradedPushforwardCharts_compatible :
    InternalHom.RestrictionHomCompatible (fun i => (U i).property.fromSpec)
      ((Scheme.Modules.pushforward (formalGradedProjection f I)).obj P) F.gradedUnderlying
      (fun i => (formalGradedPushforwardChartIso f I F (U i) P (e i)).hom) := by
  exact formalGradedPushforwardChartsCompatibilityProof f I F U P q e he

include hU q he in
/-- The actual direct image of the constructed coefficient is the original
coproduct, with no separately assumed realization or restriction compatibility. -/
def formalGradedPushforwardIsoOnCover :
    (Scheme.Modules.pushforward (formalGradedProjection f I)).obj P ≅ F.gradedUnderlying := by
  let (Z : X.Opens) : Algebra A Γ(X, Z) := formalGradedSectionAlgebra f Z
  have hc : ∀ x : X, ∃ i, ∃ y, (U i).property.fromSpec y = x := by
    intro x
    obtain ⟨i, hi⟩ := hU x
    have hi' : x ∈ Set.range (U i).property.fromSpec := by
      rw [(U i).property.range_fromSpec]
      exact hi
    exact ⟨i, hi'⟩
  exact InternalHom.glueRestrictionIso (fun i => Spec Γ(X, U i))
    (fun i => (U i).property.fromSpec) hc _ _
    (fun i => formalGradedPushforwardChartIso f I F (U i) P (e i))
    (formalGradedPushforwardCharts_compatible f I F U P q e he)

/-- The global direct-image comparison retains each original affine comparison. -/
@[reassoc]
theorem formalGradedPushforwardIsoOnCover_restrict (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).property.fromSpec).map
      (formalGradedPushforwardIsoOnCover f I F U hU P q e he).hom =
      (formalGradedPushforwardChartIso f I F (U i) P (e i)).hom := by
  let (Z : X.Opens) : Algebra A Γ(X, Z) := formalGradedSectionAlgebra f Z
  dsimp only [formalGradedPushforwardIsoOnCover]
  exact InternalHom.glueRestrictionIso_hom_restrict
    (fun j => Spec Γ(X, U j)) (fun j => (U j).property.fromSpec) _ _ _ _ _ i

/-- Existence of a genuine coherent geometric realization of the formal graded
coefficient. The only finiteness hypotheses concern the original scheme and base. -/
theorem exists_formalGradedRealization [IsNoetherianRing A] [LocallyOfFiniteType f]
    [CompactSpace X] :
    ∃ G : QuasiCoherent.FiniteTypeSheaves (formalGradedSpace f I),
      Nonempty ((Scheme.Modules.pushforward (formalGradedProjection f I)).obj G.obj ≅
        F.gradedUnderlying) := by
  let (Z : X.Opens) : Algebra A Γ(X, Z) := formalGradedSectionAlgebra f Z
  obtain ⟨ι, hι, U, hU, _⟩ := exists_formalGradedChartCover_with_base f I
  let : Finite ι := hι
  obtain ⟨G, q, hq, e, he⟩ := exists_formalGradedCoherentQuotient_on_cover f I F U hU
  let : Epi q := hq
  exact ⟨G, ⟨formalGradedPushforwardIsoOnCover f I F U hU G.obj q e he⟩⟩

end AlgebraicGeometry.Scheme.Cohomology
