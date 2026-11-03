/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.OriginalCaseOneStep
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseTwoChildGenerators
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.QuadraticClassification.Core
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.ExceptionalHilbert.FirstPower
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.BlowupChildren
public import Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.RingEquiv

/-!
# Genuine geometry and complete cones on the original path

The initial full cone is finite input. Actual original successor geometry
constructs every later full cone, using rational first-power numerics rather
than assuming later canonical frames, Hilbert functions or Gorensteinness.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing Localization.Away
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint

private theorem original_path_local_properties
    (P : Arc.ClosedPointBlowupPath.{u})
    [IsIntegrallyClosed (P.localRing 0)]
    (hA : IsNagataRing.{u, 0} (P.localRing 0))
    (hd : ringKrullDim (P.localRing 0) = 2)
    (hRat : NormalModificationH1Vanishing (P.localRing 0))
    (hsing : ∀ n, ¬ IsRegularLocalRing (P.localRing n)) (n : ℕ) :
    IsIntegrallyClosed (P.localRing n) ∧
      IsNagataRing.{u, 0} (P.localRing n) ∧
      ringKrullDim (P.localRing n) = 2 ∧
      NormalModificationH1Vanishing (P.localRing n) := by
  induction n with
  | zero => exact ⟨inferInstance, hA, hd, hRat⟩
  | succ n ih =>
    obtain ⟨hnormal, hNagata, hdim, hRational⟩ := ih
    let : IsIntegrallyClosed (P.localRing n) := hnormal
    let A : Type u := P.localRing n
    let C : Type u := P.localRing (n + 1)
    obtain ⟨_, _, yD, _, _, _, ε, _, _⟩ :=
      PointLocalization.exists_closed_point_stalkIso
        (P.point n) (P.point_closed n) (P.datum n)
        (P.point (n + 1)) (P.point_closed (n + 1)) (P.point_down n)
    let Y := MaximalIdealBlowup.source A hdim
    let yS : Y := yD
    let S : Type u := Y.presheaf.stalk yS
    let : IsLocalRing S := Y.toLocallyRingedSpace.isLocalRing yS
    let e : C ≃+* S := ε.commRingCatIsoToRingEquiv
    have hs : ¬ IsRegularLocalRing S := by
      intro h
      let : IsRegularLocalRing S := h
      exact hsing (n + 1) (IsRegularLocalRing.of_ringEquiv e.symm)
    have hproperties := singular_stalk_properties_of_rational_model A hNagata hdim hRational
      (MaximalIdealBlowup.map A hdim)
      (MaximalIdealBlowup.ordinary_normalStalks A hdim hNagata hRational)
      (MaximalIdealBlowup.map_fieldMap_isIso A hdim) yS hs
    obtain ⟨hDomainS, hNormalS, _, hNagataS, hdS, _, _, _, _, hRatS⟩ := hproperties
    let : IsDomain S := hDomainS
    let : IsIntegrallyClosed S := hNormalS
    let : Algebra S C := e.symm.toRingHom.toAlgebra
    let : Module.Finite S C := RingHom.Finite.of_surjective
      e.symm.toRingHom e.symm.surjective
    refine ⟨IsIntegrallyClosed.of_equiv e.symm, hNagataS.of_finite, ?_, ?_⟩
    · exact (ringKrullDim_eq_of_ringEquiv (R := C) (S := S) e).trans hdS
    · exact (normalModificationH1Vanishing_iff_of_ringEquiv e).mpr hRatS

/-- On the same nonregular original path, one initial complete quadratic cone
produces all later original cones and rational surface properties. No future
Hilbert, kernel, marking or Gorenstein premise is supplied. -/
theorem original_path_geometry_and_cones
    (P : Arc.ClosedPointBlowupPath.{u})
    [IsIntegrallyClosed (P.localRing 0)]
    (hA : IsNagataRing.{u, 0} (P.localRing 0))
    (hd : ringKrullDim (P.localRing 0) = 2)
    (hRat : NormalModificationH1Vanishing (P.localRing 0))
    (hsing : ∀ n, ¬ IsRegularLocalRing (P.localRing n))
    (t0 : maximalIdeal (P.localRing 0))
    (g0 : Fin 2 → maximalIdeal (P.localRing 0))
    (hgen0 : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators t0 g0 i : P.localRing 0)) = maximalIdeal (P.localRing 0))
    (q0 : MvPolynomial (Fin 3) (ResidueField (P.localRing 0)))
    (hq00 : q0 ≠ 0) (hq0 : q0.IsHomogeneous 2)
    (hker0 : RingHom.ker (CaseOne.canonicalConeMap t0 g0) = Ideal.span {q0}) (n : ℕ) :
    IsIntegrallyClosed (P.localRing n) ∧
      IsNagataRing.{u, 0} (P.localRing n) ∧
      ringKrullDim (P.localRing n) = 2 ∧
      NormalModificationH1Vanishing (P.localRing n) ∧
      Module.finrank (ResidueField (P.localRing n)) (CotangentSpace (P.localRing n)) = 3 ∧
      ∃ (t : maximalIdeal (P.localRing n)) (g : Fin 2 → maximalIdeal (P.localRing n))
          (q : MvPolynomial (Fin 3) (ResidueField (P.localRing n))),
        Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t g i : P.localRing n)) =
          maximalIdeal (P.localRing n) ∧
        q ≠ 0 ∧ q.IsHomogeneous 2 ∧
        RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q} := by
  have hgeometry := original_path_local_properties P hA hd hRat hsing
  have hcones : ∀ k, ∃ (t : maximalIdeal (P.localRing k))
      (g : Fin 2 → maximalIdeal (P.localRing k))
      (q : MvPolynomial (Fin 3) (ResidueField (P.localRing k))),
      Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t g i : P.localRing k)) =
        maximalIdeal (P.localRing k) ∧
      q ≠ 0 ∧ q.IsHomogeneous 2 ∧
      RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q} := by
    intro k
    induction k with
    | zero => exact ⟨t0, g0, q0, hgen0, hq00, hq0, hker0⟩
    | succ k ih =>
      obtain ⟨hnormal, hNagata, hdim, hRational⟩ := hgeometry k
      obtain ⟨hnormalNext, hNagataNext, hdimNext, hRationalNext⟩ := hgeometry (k + 1)
      let : IsIntegrallyClosed (P.localRing k) := hnormal
      let : IsIntegrallyClosed (P.localRing (k + 1)) := hnormalNext
      obtain ⟨t, g, q, hgen, hq0, hq, hker⟩ := ih
      obtain hcase | hcase :=
        MaximalIdealBlowup.exceptional_original_quadratic_alternatives_of_quadratic_kernel
          (P.localRing k) hdim hNagata hRational (hsing k) t g hgen q hq0 hq hker
      · obtain ⟨t, g, q, hgen, hq0, hq, hker, _, _, _, _, hns, _⟩ := hcase
        obtain ⟨t', g', q', hgen', hq'0, hq', hker', hr0, hrns⟩ :=
          OriginalCaseOneStep.exists_good_parameter
            (P.point k) (P.point_closed k) (P.datum k)
            (P.point (k + 1)) (P.point_closed (k + 1)) (P.point_down k) (hsing (k + 1))
            t g hgen q hq0 hq hker hns
        obtain ⟨p, gNext, qNext, _, hgenNext, _, _, _, hqNext0, hqNext, hkerNext, _⟩ :=
          OriginalCaseOneStep.exists_fixed_parameter_successor
            (P.point k) (P.point_closed k) hdim hNagata hRational (P.datum k)
            (P.point (k + 1)) (P.point_closed (k + 1)) (P.point_down k) (hsing (k + 1))
            t' g' hgen' q' hq'0 hq' hker' hr0 hrns
        exact ⟨p, gNext, qNext, hgenNext, hqNext0, hqNext, hkerNext⟩
      · obtain ⟨t, s, z, hgen, hker, F, _, _⟩ := hcase
        obtain ⟨_, p, u, v, hgenNext, hcotNext, _⟩ :=
          CaseTwoChildGenerators.exists_original_generators
            (P.point k) (P.point_closed k) (P.datum k)
            (P.point (k + 1)) (P.point_closed (k + 1)) (P.point_down k)
            t s z hgen hker F (hsing (k + 1))
        have hHilbert := MaximalIdealBlowup.exceptional_hilbert_of_cotangent_finrank_three
          (P.localRing (k + 1)) hdimNext hNagataNext hRationalNext hcotNext
        let C : Type u := P.localRing (k + 1)
        let : IsLocalRing C :=
          (P.scheme (k + 1)).toLocallyRingedSpace.isLocalRing (P.point (k + 1))
        let pC : maximalIdeal C := p
        let uC : maximalIdeal C := u
        let vC : maximalIdeal C := v
        have hgenOrd : Ideal.span (Set.range fun i =>
            (CaseOne.orderedGenerators pC ![uC, vC] i : C)) = maximalIdeal C := by
          change Ideal.span (Set.range ((Subtype.val : maximalIdeal C → C) ∘
            (Fin.cons pC ![uC, vC] : Fin 3 → maximalIdeal C))) = maximalIdeal C
          rw [Set.range_comp, Fin.range_cons, Matrix.range_cons_cons_empty,
            Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
          exact hgenNext.symm
        obtain ⟨qNext, hqNext0, hqNext, hkerNext, _⟩ :=
          CaseOne.exists_presentation_of_hilbert (A := C) pC ![uC, vC] hgenOrd hHilbert
        exact ⟨pC, ![uC, vC], qNext, hgenOrd, hqNext0, hqNext, hkerNext⟩
  obtain ⟨hnormal, hNagata, hdim, hRational⟩ := hgeometry n
  refine ⟨hnormal, hNagata, hdim, hRational, ?_, hcones n⟩
  obtain ⟨t, g, q, hgen, _, _, _⟩ := hcones n
  apply cotangent_finrank_eq_three_of_spanFinrank_le_three hdim (hsing n)
  rw [← hgen]
  apply (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans
  rw [← Set.image_univ]
  exact (Set.ncard_image_le (Set.finite_univ : (Set.univ : Set (Fin 3)).Finite)).trans_eq
    (by simp)

end AlgebraicGeometry.Scheme.RationalDoublePoint
