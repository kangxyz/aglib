/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseOneNonreturn.Core
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.BlowupChildren
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.ExceptionalHilbert.FirstPower
public import Aglib.RingTheory.RegularLocalRing.ThreeGenerators

/-!
# Genuine geometric Case-I fixed-parameter successors

The pure original-stalk relation, full-kernel consumer and native coverage
are imported from Core. Actual rational ordinary-blowup geometry supplies
the child surface properties. Genuine child generators give cotangent rank
three before any child Hilbert input; ordinary exceptional first-power
numerics then supply the entire Hilbert function on that literal stalk.
No inverse cohomology, child kernel, or Gorenstein/canonical geometry is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing
open Localization.Away
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.CaseOneNonreturn

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    {t : maximalIdeal A} {g : Fin 2 → maximalIdeal A} {Q : CaseOne.Plane A}
    (D : CaseOne.Presentation A t g Q) (M : Ideal (CaseOne.Plane A)) [M.IsMaximal]
    (hQM : Q ∈ M)

open AlgebraicGeometry.Scheme.RationalSingularities
open AlgebraicGeometry.Scheme.RationalSingularities.MaximalIdealBlowup

/-- Actual ordinary-blowup geometry and genuine child generators give its
full Hilbert function and fixed-parameter nonsquare kernel. No inverse-line
cohomology or child canonical/frame hypothesis is retained. -/
theorem exists_ordinary_stalk_fixed_parameter_successor
    [IsIntegrallyClosed A] (hdA : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (ht : (t : A) ≠ 0) (hQ0 : Q ≠ 0) (hdeg : Q.totalDegree ≤ 2)
    (hcase : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ l : CaseOne.Plane A,
      l.totalDegree ≤ 1 ∧ Q = MvPolynomial.C c * l ^ 2)
    (hsing : ¬ IsRegularLocalRing
      ((datum A).Y.presheaf.stalk (CaseOneChart.point (datum A) D M hQM))) :
    let S : Type u := (datum A).Y.presheaf.stalk (CaseOneChart.point (datum A) D M hQM)
    let f : A →+* S := (datum A).map.stalkScalar (CaseOneChart.point (datum A) D M hQM)
    let _ : IsLocalHom f := CaseOneChart.stalkScalar_isLocal (datum A) D M hQM
    ∃ (p : maximalIdeal S) (g' : Fin 2 → maximalIdeal S)
        (q : MvPolynomial (Fin 3) (ResidueField S)),
      (p : S) = f (t : A) ∧
      Ideal.span (Set.range fun i => (CaseOne.orderedGenerators p g' i : S)) =
        maximalIdeal S ∧
      (p : S) ∉ maximalIdeal S ^ 2 ∧
      (maximalIdeal A).map f = Ideal.span {(p : S)} ∧
      Function.Bijective (ResidueField.map f) ∧
      q ≠ 0 ∧ q.IsHomogeneous 2 ∧
      RingHom.ker (CaseOne.canonicalConeMap p g') = Ideal.span {q} ∧
      (¬ ∃ L : MvPolynomial (Fin 3) (ResidueField S),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        RingHom.ker (CaseOne.canonicalConeMap p g') = Ideal.span {L ^ 2}) ∧
      (MvPolynomial.eval₂Hom
        (MvPolynomial.C : ResidueField S →+* MvPolynomial (Fin 2) (ResidueField S))
        ![0, MvPolynomial.X 0, MvPolynomial.X 1] q ≠ 0) ∧
      (¬ ∃ c : ResidueField S, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField S),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q =
          MvPolynomial.C c * L ^ 2) ∧
      MvPolynomial.FirstCoordinate.dehom q ≠ 0 ∧
      (MvPolynomial.FirstCoordinate.dehom q).totalDegree ≤ 2 ∧
      (¬ ∃ c : ResidueField S, c ≠ 0 ∧ ∃ l : CaseOne.Plane S,
        l.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q =
          MvPolynomial.C c * l ^ 2) ∧
      Nonempty (CaseOne.Presentation S p g' (MvPolynomial.FirstCoordinate.dehom q)) := by
  let x : source A hdA := CaseOneChart.point (datum A) D M hQM
  let S : Type u := (source A hdA).presheaf.stalk x
  obtain ⟨hDomain, hNormal, hNoeth, hNagata, hdS, _, _, _, _, hRatS⟩ :=
    singular_stalk_properties_of_rational_model A hA hdA hRat (map A hdA)
      (ordinary_normalStalks A hdA hA hRat) (map_fieldMap_isIso A hdA) x hsing
  let _ : IsDomain S := hDomain
  let _ : IsIntegrallyClosed S := hNormal
  let _ : IsNoetherianRing S := hNoeth
  obtain ⟨_, _, _, p, u, v, _, _, _, _, _, _, _, _, _, _, _, hgenS, _⟩ :=
    exists_original_stalk_quadratic_relation (datum A) D M hQM ht hQ0 hdeg hcase hsing
  have hcot := cotangent_finrank_eq_three_of_maximalIdeal_span_triple
    hdS hsing p.val u.val v.val hgenS
  have hHilbert := exceptional_hilbert_of_cotangent_finrank_three S hdS hNagata hRatS hcot
  exact exists_original_stalk_fixed_parameter_successor_of_hilbert
    (datum A) D M hQM ht hQ0 hdeg hcase hsing hHilbert

/-- Every actual singular child of the ordinary blowup preserves the same
good original parameter. Closedness, rational surface properties, rank three
and the full child Hilbert function are all derived, not supplied as oracles. -/
theorem exists_ordinary_fixed_parameter_successor_at_singular_point
    [IsIntegrallyClosed A] (hdA : ringKrullDim A = 2)
    (hA : IsNagataRing.{u, 0} A) (hRat : NormalModificationH1Vanishing A)
    (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators t g i : A)) = maximalIdeal A)
    (q : MvPolynomial (Fin 3) (ResidueField A)) (hq0 : q ≠ 0) (hq : q.IsHomogeneous 2)
    (hker : RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q})
    (hr0 : MvPolynomial.eval₂Hom
      (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 2) (ResidueField A))
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q ≠ 0)
    (hrns : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField A),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q =
        MvPolynomial.C c * L ^ 2)
    (x : source A hdA)
    (hsing : ¬ IsRegularLocalRing ((source A hdA).presheaf.stalk x)) :
    ∃ hbase : map A hdA x = closedPoint A,
    let S : Type u := (source A hdA).presheaf.stalk x
    let f : A →+* S := (map A hdA).stalkScalar x
    let _ : IsLocalHom f := (map A hdA).stalkScalar_isLocalHom_of_closedPoint x hbase
    ∃ (p : maximalIdeal S) (g' : Fin 2 → maximalIdeal S)
        (q : MvPolynomial (Fin 3) (ResidueField S)),
      (p : S) = f (t : A) ∧
      Ideal.span (Set.range fun i => (CaseOne.orderedGenerators p g' i : S)) =
        maximalIdeal S ∧
      (p : S) ∉ maximalIdeal S ^ 2 ∧
      (maximalIdeal A).map f = Ideal.span {(p : S)} ∧
      Function.Bijective (ResidueField.map f) ∧
      q ≠ 0 ∧ q.IsHomogeneous 2 ∧
      RingHom.ker (CaseOne.canonicalConeMap p g') = Ideal.span {q} ∧
      (¬ ∃ L : MvPolynomial (Fin 3) (ResidueField S),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        RingHom.ker (CaseOne.canonicalConeMap p g') = Ideal.span {L ^ 2}) ∧
      (MvPolynomial.eval₂Hom
        (MvPolynomial.C : ResidueField S →+* MvPolynomial (Fin 2) (ResidueField S))
        ![0, MvPolynomial.X 0, MvPolynomial.X 1] q ≠ 0) ∧
      (¬ ∃ c : ResidueField S, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField S),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q =
          MvPolynomial.C c * L ^ 2) ∧
      MvPolynomial.FirstCoordinate.dehom q ≠ 0 ∧
      (MvPolynomial.FirstCoordinate.dehom q).totalDegree ≤ 2 ∧
      (¬ ∃ c : ResidueField S, c ≠ 0 ∧ ∃ l : CaseOne.Plane S,
        l.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q =
          MvPolynomial.C c * l ^ 2) ∧
      Nonempty (CaseOne.Presentation S p g' (MvPolynomial.FirstCoordinate.dehom q)) := by
  obtain ⟨_, _, _, _, _, hx, _, hbase, _, _⟩ :=
    singular_stalk_properties_of_rational_model A hA hdA hRat (map A hdA)
      (ordinary_normalStalks A hdA hA hRat) (map_fieldMap_isIso A hdA) x hsing
  have ht : (t : A) ≠ 0 := CaseOne.denominator_ne_zero_of_kernel t g q hq0 hq hker
  have hQ0 : MvPolynomial.FirstCoordinate.dehom q ≠ 0 := by
    intro hz
    apply hq0
    apply MvPolynomial.FirstCoordinate.dehom_injective_on_homogeneous_two hq
      (MvPolynomial.isHomogeneous_zero (Fin 3) (ResidueField A) 2)
    simpa only [map_zero] using hz
  have hdeg : (MvPolynomial.FirstCoordinate.dehom q).totalDegree ≤ 2 := by
    rw [GradedAlgebra.TernaryQuadratic.eq_quadratic_of_homogeneous hq]
    exact GradedAlgebra.TernaryQuadratic.dehom_quadratic_totalDegree _
  have hns := MvPolynomial.not_scalar_homogeneous_square_of_first_zero_restriction q hr0 hrns
  have hcase : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : CaseOne.Plane A,
      L.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q = MvPolynomial.C c * L ^ 2 :=
    fun h => hns ((MvPolynomial.FirstCoordinate.scalar_linear_square_iff hq hq0).mp h)
  let D' := CaseOne.presentationOfKernel t g hgen q hker
  have hg : ![g 0, g 1] = g := by
    funext i
    fin_cases i <;> rfl
  have hgenPair : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators t ![g 0, g 1] i : A)) = maximalIdeal A := by
    rw [hg]
    exact hgen
  have hkerPair : RingHom.ker (CaseOne.canonicalConeMap t ![g 0, g 1]) = Ideal.span {q} := by
    rw [hg]
    exact hker
  have hchart := mem_parameterChart_of_closed_singular_point (datum A) t (g 0) (g 1)
    hgenPair q hq0 hq hkerPair hr0 hrns x hx hbase hsing
  obtain ⟨M', hM', hQM', hpoint⟩ := CaseOneChart.exists_plane_point (datum A) D' x hx hbase hchart
  let _ : M'.IsMaximal := hM'
  refine ⟨hbase, ?_⟩
  subst x
  exact exists_ordinary_stalk_fixed_parameter_successor D' M' hQM'
    hdA hA hRat ht hQ0 hdeg hcase hsing

end AlgebraicGeometry.Scheme.RationalDoublePoint.CaseOneNonreturn
