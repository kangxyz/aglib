/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.CaseOneCharts
public import Aglib.AlgebraicGeometry.Blowup.GeneratorAtlas
public import Aglib.RingTheory.Blowup.CaseOne.Successor
public import Aglib.RingTheory.LocalRing.ParameterEquiv

/-!
# Original-stalk Case-I nonreturn and actual chart coverage

The genuine centered relation and literal generators are derived on the
original scheme stalk. Honest all-degree Hilbert data supply its entire
canonical kernel and fixed-parameter nonreturn. The native generator atlas,
original point fractions and both opposite-chart overlaps give coverage.
Initial goodness uses an actual singular child, not a generic hyperplane.
The genuine Projective cohomology supplier belongs to the downstream wrapper.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory IsLocalRing
open Localization.Away
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint.CaseOneNonreturn

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (B : BlowupDatum (affineCenter A (maximalIdeal A)))
    {t : maximalIdeal A} {g : Fin 2 → maximalIdeal A} {Q : CaseOne.Plane A}
    (D : CaseOne.Presentation A t g Q) (M : Ideal (CaseOne.Plane A)) [M.IsMaximal]
    (hQM : Q ∈ M)

/-- The actual original scheme stalk receives the true centered relation,
literal shifted-fraction generators and the unchanged original parameter.
Global closedness is not inferred from chart maximality or asserted here. -/
theorem exists_original_stalk_quadratic_relation
    (ht : (t : A) ≠ 0) (hQ0 : Q ≠ 0) (hdeg : Q.totalDegree ≤ 2)
    (hcase : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ l : CaseOne.Plane A,
      l.totalDegree ≤ 1 ∧ Q = MvPolynomial.C c * l ^ 2)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk (CaseOneChart.point B D M hQM))) :
    let S : Type u := B.Y.presheaf.stalk (CaseOneChart.point B D M hQM)
    let ε : S ≃+* D.LocalRing M hQM :=
      (CaseOneChart.stalkIso B D M hQM).commRingCatIsoToRingEquiv
    let f : A →+* S := B.map.stalkScalar (CaseOneChart.point B D M hQM)
    let _ : IsLocalHom f := CaseOneChart.stalkScalar_isLocal B D M hQM
    ∃ (α : Fin 2 → ResidueField A) (a : Fin 2 → A) (b : Fin 3 → A)
        (p u v : maximalIdeal S) (d e z : S),
      M = RingHom.ker (MvPolynomial.eval α) ∧
      (∀ i, IsLocalRing.residue A (a i) = α i) ∧
      IsLocalRing.residue A (b 0) = Q.coeff (Finsupp.single 0 2) ∧
      IsLocalRing.residue A (b 1) = Q.coeff (Finsupp.single 0 1 + Finsupp.single 1 1) ∧
      IsLocalRing.residue A (b 2) = Q.coeff (Finsupp.single 1 2) ∧
      (u : S) = ε.symm (algebraMap (CaseOne.Chart A t) (D.LocalRing M hQM)
        (CaseOne.centeredFraction t g a 0)) ∧
      (v : S) = ε.symm (algebraMap (CaseOne.Chart A t) (D.LocalRing M hQM)
        (CaseOne.centeredFraction t g a 1)) ∧
      (p : S) = f (t : A) ∧
      maximalIdeal S = Ideal.span ({(p : S), (u : S), (v : S)} : Set S) ∧
      (p : S) ∉ maximalIdeal S ^ 2 ∧
      (maximalIdeal A).map f = Ideal.span {(p : S)} ∧
      Function.Bijective (ResidueField.map f) ∧
      -d * (p : S) ^ 2 + f (b 0) * (u : S) ^ 2 + f (b 2) * (v : S) ^ 2 +
        -e * (p : S) * (u : S) + -z * (p : S) * (v : S) +
        f (b 1) * (u : S) * (v : S) = 0 := by
  let S : Type u := B.Y.presheaf.stalk (CaseOneChart.point B D M hQM)
  let R := D.LocalRing M hQM
  let ε : S ≃+* R := (CaseOneChart.stalkIso B D M hQM).commRingCatIsoToRingEquiv
  let f : A →+* S := B.map.stalkScalar (CaseOneChart.point B D M hQM)
  let c : A →+* R := D.localMap M hQM
  let _ : IsLocalHom f := CaseOneChart.stalkScalar_isLocal B D M hQM
  let _ : IsLocalHom c := D.localMap_isLocal M hQM
  have hε : ε.toRingHom.comp f = c := CaseOneChart.stalkIso_stalkScalar B D M hQM
  have hεbase (a : A) : ε.symm (D.localMap M hQM a) = f a :=
    ε.injective ((ε.apply_symm_apply (c a)).trans (RingHom.congr_fun hε a).symm)
  have hs : ¬ IsRegularLocalRing R :=
    fun h => hsing ((CaseOneChart.isRegular_iff B D M hQM).mpr h)
  obtain ⟨α, a, b, uR, vR, dR, eR, zR, hM, ha, hb0, hb1, hb2, huR, hvR,
      hgenR, _, hrelR⟩ := D.exists_centered_local_quadratic_relation M hQM ht hQ0 hdeg hcase hs
  have hm : (maximalIdeal R).map ε.symm.toRingHom = maximalIdeal S :=
    map_maximalIdeal_of_surjective ε.symm.toRingHom ε.symm.surjective
  have hmem (w : maximalIdeal R) : ε.symm (w : R) ∈ maximalIdeal S := by
    rw [← hm]
    exact Ideal.mem_map_of_mem ε.symm.toRingHom w.property
  let p : maximalIdeal S := ⟨ε.symm (D.parameter M hQM),
    hmem ⟨D.parameter M hQM, D.parameter_mem_maximal M hQM⟩⟩
  let u : maximalIdeal S := ⟨ε.symm (uR : R), hmem uR⟩
  let v : maximalIdeal S := ⟨ε.symm (vR : R), hmem vR⟩
  let d : S := ε.symm dR
  let e : S := ε.symm eR
  let z : S := ε.symm zR
  have hgen : maximalIdeal S = Ideal.span ({(p : S), (u : S), (v : S)} : Set S) := by
    have h := congrArg (Ideal.map ε.symm.toRingHom) hgenR
    rw [hm, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at h
    exact h
  have hep : ε.toRingHom (p : S) = c (t : A) := by
    change ε (ε.symm (D.parameter M hQM)) = c (t : A)
    rw [ε.apply_symm_apply]
    rfl
  have hmin : c (t : A) ∉ maximalIdeal R ^ 2 :=
    D.parameter_not_mem_sq M hQM ht hQ0 hs
  have hcenter : (maximalIdeal A).map c = Ideal.span {c (t : A)} := D.centre M hQM
  have hres : Function.Bijective (ResidueField.map c) :=
    D.residue_map_bijective M hQM ht hQ0 hdeg hcase hs
  have htransport := parameter_properties_of_equiv_comp f c ε hε (t : A) (p : S) hep
  have htransport_min := htransport hmin
  have htransport_center := htransport_min hcenter
  obtain ⟨hp, hpmin, hpcenter, hpres⟩ := htransport_center hres
  have hu : (u : S) = ε.symm (algebraMap (CaseOne.Chart A t) R
      (CaseOne.centeredFraction t g a 0)) := congrArg ε.symm huR
  have hv : (v : S) = ε.symm (algebraMap (CaseOne.Chart A t) R
      (CaseOne.centeredFraction t g a 1)) := congrArg ε.symm hvR
  have hεp : ε.symm (D.parameter M hQM) = (p : S) := rfl
  have hεu : ε.symm (uR : R) = (u : S) := rfl
  have hεv : ε.symm (vR : R) = (v : S) := rfl
  have hrel : -d * (p : S) ^ 2 + f (b 0) * (u : S) ^ 2 + f (b 2) * (v : S) ^ 2 +
      -e * (p : S) * (u : S) + -z * (p : S) * (v : S) +
      f (b 1) * (u : S) * (v : S) = 0 := by
    simpa only [map_add, map_mul, map_pow, map_neg, map_zero, hεbase, hεp, hεu, hεv,
      d, e, z] using congrArg ε.symm hrelR
  exact ⟨α, a, b, p, u, v, d, e, z, hM, ha, hb0, hb1, hb2, hu, hv,
    hp, hgen, hpmin, hpcenter, hpres, hrel⟩

/-- The original residue-field action on a maximal-ideal associated-graded component. -/
local instance originalStalkComponentModule (R : Type u) [CommRing R] [IsLocalRing R]
    (n : ℕ) : Module (ResidueField R)
      (Ideal.associatedGradedQuotientGrading (maximalIdeal R) n) :=
  Submodule.module (Ideal.associatedGradedQuotientGrading (maximalIdeal R) n)

/-- The actual relation and the genuine original-stalk Hilbert function
produce the whole successor kernel and preserve the same good parameter. -/
theorem exists_original_stalk_fixed_parameter_successor_of_hilbert
    (ht : (t : A) ≠ 0) (hQ0 : Q ≠ 0) (hdeg : Q.totalDegree ≤ 2)
    (hcase : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ l : CaseOne.Plane A,
      l.totalDegree ≤ 1 ∧ Q = MvPolynomial.C c * l ^ 2)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk (CaseOneChart.point B D M hQM)))
    (hHilbert : ∀ n, Module.finrank
      (ResidueField (B.Y.presheaf.stalk (CaseOneChart.point B D M hQM)))
      (Ideal.associatedGradedQuotientGrading
        (maximalIdeal (B.Y.presheaf.stalk (CaseOneChart.point B D M hQM))) n) =
          2 * n + 1) :
    let S : Type u := B.Y.presheaf.stalk (CaseOneChart.point B D M hQM)
    let f : A →+* S := B.map.stalkScalar (CaseOneChart.point B D M hQM)
    let _ : IsLocalHom f := CaseOneChart.stalkScalar_isLocal B D M hQM
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
  let S : Type u := B.Y.presheaf.stalk (CaseOneChart.point B D M hQM)
  let f : A →+* S := B.map.stalkScalar (CaseOneChart.point B D M hQM)
  let _ : IsLocalHom f := CaseOneChart.stalkScalar_isLocal B D M hQM
  obtain ⟨α, _, b, p, u, v, d, e, z, hM, _, hb0, hb1, hb2, _, _,
      hp, hgen, hpmin, hpcenter, hpres, hrel⟩ :=
    exists_original_stalk_quadratic_relation B D M hQM ht hQ0 hdeg hcase hsing
  let c : Fin 6 → S := ![-d, f (b 0), f (b 2), -e, -z, f (b 1)]
  let q := GradedAlgebra.TernaryQuadratic.quadratic (fun i => IsLocalRing.residue S (c i))
  let ρ : ResidueField A →+* ResidueField S := ResidueField.map f
  have h1 : IsLocalRing.residue S (c 1) = ρ (Q.coeff (Finsupp.single 0 2)) := by
    change IsLocalRing.residue S (f (b 0)) = ResidueField.map f _
    rw [← hb0, ResidueField.map_residue]
  have h5 : IsLocalRing.residue S (c 5) = ρ (Q.coeff
      (Finsupp.single 0 1 + Finsupp.single 1 1)) := by
    change IsLocalRing.residue S (f (b 1)) = ResidueField.map f _
    rw [← hb1, ResidueField.map_residue]
  have h2 : IsLocalRing.residue S (c 2) = ρ (Q.coeff (Finsupp.single 1 2)) := by
    change IsLocalRing.residue S (f (b 2)) = ResidueField.map f _
    rw [← hb2, ResidueField.map_residue]
  have hQsq := CaseOneChart.equation_mem_sq_of_singular_stalk B D M hQM ht hsing
  rw [hM] at hQsq
  obtain ⟨hr0, hrns⟩ :=
    GradedAlgebra.TernaryQuadratic.restrict_zero_nonsquare_of_centered_coefficients
      ρ hpres Q hQ0 hdeg α hQsq hcase (fun i => IsLocalRing.residue S (c i)) h1 h5 h2
  have hq0 : q ≠ 0 := by
    intro hz
    apply hr0
    change MvPolynomial.eval₂Hom
      (MvPolynomial.C : ResidueField S →+* MvPolynomial (Fin 2) (ResidueField S))
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q = 0
    rw [hz, map_zero]
  have hc : (fun i => IsLocalRing.residue S (c i)) ≠ 0 := by
    intro hz
    apply hq0
    change GradedAlgebra.TernaryQuadratic.quadratic
      (fun i => IsLocalRing.residue S (c i)) = 0
    rw [hz]
    simp only [GradedAlgebra.TernaryQuadratic.quadratic, Pi.zero_apply,
      map_zero, Finset.sum_const_zero]
  have hgen' : Ideal.span
      (Set.range fun i => (CaseOne.orderedGenerators p ![u, v] i : S)) = maximalIdeal S := by
    have hr : Set.range (fun i => (CaseOne.orderedGenerators p ![u, v] i : S)) =
        {(p : S), (u : S), (v : S)} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [CaseOne.orderedGenerators]
      · intro hx
        rcases hx with hx | hx | hx
        · exact ⟨0, hx.symm⟩
        · exact ⟨1, hx.symm⟩
        · exact ⟨2, hx.symm⟩
    rw [hr]
    exact hgen.symm
  have hker := CaseOne.canonicalCone_kernel_eq_of_quadratic_relation p u v c
    hgen' hc hrel hHilbert
  have hq : q.IsHomogeneous 2 := GradedAlgebra.TernaryQuadratic.quadratic_homogeneous _
  have hns := MvPolynomial.not_scalar_homogeneous_square_of_first_zero_restriction q hr0 hrns
  have hnonreturn : ¬ ∃ L : MvPolynomial (Fin 3) (ResidueField S),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      RingHom.ker (CaseOne.canonicalConeMap p ![u, v]) = Ideal.span {L ^ 2} := by
    rintro ⟨L, hL, hL0, hkL⟩
    have hmem : q ∈ Ideal.span {L ^ 2} := by
      rw [← hkL, hker]
      exact Ideal.mem_span_singleton_self q
    obtain ⟨a, ha, he⟩ := MvPolynomial.eq_nonzero_scalar_mul_of_mem_span_of_isHomogeneous
      hq hq0 (hL.pow 2) (pow_ne_zero 2 hL0) hmem
    exact hns ⟨a, ha, L, hL, hL0, he⟩
  have hcase' : ¬ ∃ c : ResidueField S, c ≠ 0 ∧ ∃ l : CaseOne.Plane S,
      l.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q =
        MvPolynomial.C c * l ^ 2 :=
    fun h => hns ((MvPolynomial.FirstCoordinate.scalar_linear_square_iff hq hq0).mp h)
  exact ⟨p, ![u, v], q, hp, hgen', hpmin, hpcenter, hpres, hq0, hq, hker, hnonreturn,
    hr0, hrns, GradedAlgebra.TernaryQuadratic.dehom_quadratic_ne_zero _ hc,
    GradedAlgebra.TernaryQuadratic.dehom_quadratic_totalDegree _, hcase',
    ⟨CaseOne.presentationOfKernel p ![u, v] hgen' q hker⟩⟩

/-- A parameter chart containing an actual singular Case-I child is good:
its original homogeneous equation has a nonzero nonsquare binary restriction.
No generic hyperplane or rational-point existence over the field is used. -/
theorem good_first_parameter_of_singular_stalk
    {q : MvPolynomial (Fin 3) (ResidueField A)} (hq : q.IsHomogeneous 2)
    (D' : CaseOne.Presentation A t g (MvPolynomial.FirstCoordinate.dehom q))
    (M' : Ideal (CaseOne.Plane A)) [M'.IsMaximal]
    (hQM' : MvPolynomial.FirstCoordinate.dehom q ∈ M')
    (ht : (t : A) ≠ 0) (hQ0 : MvPolynomial.FirstCoordinate.dehom q ≠ 0)
    (hdeg : (MvPolynomial.FirstCoordinate.dehom q).totalDegree ≤ 2)
    (hcase : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ l : CaseOne.Plane A,
      l.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q = MvPolynomial.C c * l ^ 2)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk (CaseOneChart.point B D' M' hQM'))) :
    MvPolynomial.eval₂Hom
      (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 2) (ResidueField A))
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q ≠ 0 ∧
    ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField A),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q =
        MvPolynomial.C c * L ^ 2 := by
  have hs : ¬ IsRegularLocalRing (D'.LocalRing M' hQM') :=
    fun h => hsing ((CaseOneChart.isRegular_iff B D' M' hQM').mpr h)
  obtain ⟨α, hM⟩ := D'.exists_rational_coordinates M' hQM' ht hQ0 hdeg hcase hs
  have hQsq := D'.equation_mem_sq_of_not_regular M' hQM' ht hs
  rw [hM] at hQsq
  have he := MvPolynomial.FirstCoordinate.restrict_zero_eq_centered_binary q hq hdeg α hQsq
  obtain ⟨hr0, _, hrns⟩ := MvPolynomial.centered_binary_quadratic_nonsquare
    (MvPolynomial.FirstCoordinate.dehom q) hQ0 hdeg α hQsq hcase
  rw [he]
  exact ⟨hr0, hrns⟩

/-- An actual globally closed singular point in the first opposite chart
lies in the original good-parameter chart by the native overlap. -/
theorem mem_parameterChart_of_first_opposite_singular_point
    (t s z : maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators t ![s, z] i : A)) = maximalIdeal A)
    (q : MvPolynomial (Fin 3) (ResidueField A)) (hq0 : q ≠ 0) (hq : q.IsHomogeneous 2)
    (hker : RingHom.ker (CaseOne.canonicalConeMap t ![s, z]) = Ideal.span {q})
    (hr0 : MvPolynomial.eval₂Hom
      (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 2) (ResidueField A))
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q ≠ 0)
    (hrns : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField A),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q =
        MvPolynomial.C c * L ^ 2)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x))
    (hchart : x ∈ Set.range (CaseOneChart.chart B s)) :
    x ∈ Set.range (CaseOneChart.chart B t) := by
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
  let q' := MvPolynomial.rename e q
  have hperm : CaseOne.orderedGenerators s ![t, z] =
      fun i => CaseOne.orderedGenerators t ![s, z] (e i) := by
    funext i
    fin_cases i <;> simp [e, CaseOne.orderedGenerators, Equiv.swap_apply_def]
  have hgen' : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators s ![t, z] i : A)) = maximalIdeal A := by
    have hr : Set.range (fun i => (CaseOne.orderedGenerators s ![t, z] i : A)) =
        Set.range (fun i => (CaseOne.orderedGenerators t ![s, z] i : A)) := by
      simp only [hperm]
      exact e.surjective.range_comp (fun i => (CaseOne.orderedGenerators t ![s, z] i : A))
    rw [hr]
    exact hgen
  have hker' : RingHom.ker (CaseOne.canonicalConeMap s ![t, z]) = Ideal.span {q'} := by
    simpa only [q', e, Equiv.symm_swap] using
      CaseOne.canonicalCone_kernel_permutation t s ![s, z] ![t, z] e hperm q hker
  have hq' : q'.IsHomogeneous 2 := MvPolynomial.IsHomogeneous.rename_isHomogeneous hq
  have hq'0 : q' ≠ 0 := by
    intro hz
    exact hq0 (MvPolynomial.rename_injective e e.injective
      (hz.trans (map_zero (MvPolynomial.rename e)).symm))
  have hs : (s : A) ≠ 0 := CaseOne.denominator_ne_zero_of_kernel s ![t, z] q' hq'0 hq' hker'
  have hQ0 : MvPolynomial.FirstCoordinate.dehom q' ≠ 0 := by
    intro hz
    apply hq'0
    apply MvPolynomial.FirstCoordinate.dehom_injective_on_homogeneous_two hq'
      (MvPolynomial.isHomogeneous_zero (Fin 3) (ResidueField A) 2)
    simpa only [map_zero] using hz
  have hdeg : (MvPolynomial.FirstCoordinate.dehom q').totalDegree ≤ 2 := by
    rw [GradedAlgebra.TernaryQuadratic.eq_quadratic_of_homogeneous hq']
    exact GradedAlgebra.TernaryQuadratic.dehom_quadratic_totalDegree _
  have hns := MvPolynomial.not_scalar_homogeneous_square_of_first_zero_restriction q hr0 hrns
  have hns' : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 3) (ResidueField A),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q' = MvPolynomial.C c * L ^ 2 :=
    fun h => hns ((MvPolynomial.exists_scalar_homogeneous_square_rename_iff e q 1).mp h)
  have hcase : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : CaseOne.Plane A,
      L.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q' = MvPolynomial.C c * L ^ 2 :=
    fun h => hns' ((MvPolynomial.FirstCoordinate.scalar_linear_square_iff hq' hq'0).mp h)
  let D' := CaseOne.presentationOfKernel s ![t, z] hgen' q' hker'
  obtain ⟨M', hM', hQM', hpoint⟩ := CaseOneChart.exists_plane_point B D' x hx hbase hchart
  let _ : M'.IsMaximal := hM'
  have hs' : ¬ IsRegularLocalRing (D'.LocalRing M' hQM') := by
    intro h
    apply hsing
    rw [← hpoint]
    exact (CaseOneChart.isRegular_iff B D' M' hQM').mpr h
  have hnot := CaseOne.Presentation.first_opposite_fraction_not_mem q hq hr0 hrns
    D' M' hQM' hs hQ0 hdeg hcase hs'
  have hloc : (⟨D'.prime M' hQM', inferInstance⟩ : PrimeSpectrum (CaseOne.Chart A s)) ∈
      Set.range (affineOverlapMap A (maximalIdeal A) s t) := by
    change (⟨D'.prime M' hQM', inferInstance⟩ : PrimeSpectrum
      (affineBlowupAlgebra A (maximalIdeal A) s)) ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (affineBlowupAlgebra A (maximalIdeal A) s)
          (Localization.Away (ratio A (maximalIdeal A) s t))))
    rw [PrimeSpectrum.localization_away_comap_range
      (Localization.Away (ratio A (maximalIdeal A) s t)) (ratio A (maximalIdeal A) s t)]
    exact hnot
  obtain ⟨w, hw⟩ := hloc
  have hr : x ∈ Set.range
      (affineOverlapMap A (maximalIdeal A) s t ≫ (affineAtlas B).chart s) := by
    refine ⟨w, ?_⟩
    change CaseOneChart.chart B s (affineOverlapMap A (maximalIdeal A) s t w) = x
    rw [hw]
    exact hpoint
  rw [(affineAtlas B).overlap] at hr
  exact hr.2

/-- Every globally closed singular exceptional point lies in the same
original good-parameter chart; both opposite generators are treated. -/
theorem mem_parameterChart_of_closed_singular_point
    (t s z : maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators t ![s, z] i : A)) = maximalIdeal A)
    (q : MvPolynomial (Fin 3) (ResidueField A)) (hq0 : q ≠ 0) (hq : q.IsHomogeneous 2)
    (hker : RingHom.ker (CaseOne.canonicalConeMap t ![s, z]) = Ideal.span {q})
    (hr0 : MvPolynomial.eval₂Hom
      (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 2) (ResidueField A))
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q ≠ 0)
    (hrns : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField A),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q =
        MvPolynomial.C c * L ^ 2)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x)) :
    x ∈ Set.range (CaseOneChart.chart B t) := by
  obtain ⟨i, hi⟩ := AffineAtlas.generator_covers (CaseOne.orderedGenerators t ![s, z])
    hgen (affineAtlas B) x
  fin_cases i
  · exact hi
  · exact mem_parameterChart_of_first_opposite_singular_point B t s z hgen q hq0 hq
      hker hr0 hrns x hx hbase hsing hi
  · let e : Fin 3 ≃ Fin 3 := Equiv.swap 1 2
    let q' := MvPolynomial.rename e q
    have hperm : CaseOne.orderedGenerators t ![z, s] =
        fun i => CaseOne.orderedGenerators t ![s, z] (e i) := by
      funext i
      fin_cases i <;> simp [e, CaseOne.orderedGenerators, Equiv.swap_apply_def]
    have hgen' : Ideal.span (Set.range fun i =>
        (CaseOne.orderedGenerators t ![z, s] i : A)) = maximalIdeal A := by
      have hr : Set.range (fun i => (CaseOne.orderedGenerators t ![z, s] i : A)) =
          Set.range (fun i => (CaseOne.orderedGenerators t ![s, z] i : A)) := by
        simp only [hperm]
        exact e.surjective.range_comp (fun i => (CaseOne.orderedGenerators t ![s, z] i : A))
      rw [hr]
      exact hgen
    have hker' : RingHom.ker (CaseOne.canonicalConeMap t ![z, s]) = Ideal.span {q'} := by
      simpa only [q', e, Equiv.symm_swap] using
        CaseOne.canonicalCone_kernel_permutation t t ![s, z] ![z, s] e hperm q hker
    have hq' : q'.IsHomogeneous 2 := MvPolynomial.IsHomogeneous.rename_isHomogeneous hq
    have hq'0 : q' ≠ 0 := by
      intro hz
      exact hq0 (MvPolynomial.rename_injective e e.injective
        (hz.trans (map_zero (MvPolynomial.rename e)).symm))
    let r := MvPolynomial.eval₂Hom
      (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 2) (ResidueField A))
      ![0, MvPolynomial.X 0, MvPolynomial.X 1] q
    let eB : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
    have he : MvPolynomial.eval₂Hom
        (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 2) (ResidueField A))
        ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' = MvPolynomial.rename eB r :=
      MvPolynomial.FirstCoordinate.restrict_zero_rename_swap_companions q
    have hr0' : MvPolynomial.eval₂Hom
        (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 2) (ResidueField A))
        ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' ≠ 0 := by
      rw [he]
      intro hz
      exact hr0 (MvPolynomial.rename_injective eB eB.injective
        (hz.trans (map_zero (MvPolynomial.rename eB)).symm))
    have hrns' : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField A),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' =
          MvPolynomial.C c * L ^ 2 := by
      rw [he]
      intro h
      exact hrns ((MvPolynomial.exists_scalar_homogeneous_square_rename_iff eB r 1).mp h)
    exact mem_parameterChart_of_first_opposite_singular_point B t z s hgen' q' hq'0 hq'
      hker' hr0' hrns' x hx hbase hsing hi

/-- A real singular child selects an original generator chart whose
parameter is good. This is not a generic-hyperplane existence assertion. -/
theorem exists_good_parameter_of_closed_singular_child
    (t : maximalIdeal A) (g : Fin 2 → maximalIdeal A)
    (hgen : Ideal.span (Set.range fun i =>
      (CaseOne.orderedGenerators t g i : A)) = maximalIdeal A)
    (q : MvPolynomial (Fin 3) (ResidueField A)) (hq0 : q ≠ 0) (hq : q.IsHomogeneous 2)
    (hker : RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q})
    (hns : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 3) (ResidueField A),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q = MvPolynomial.C c * L ^ 2)
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x)) :
    ∃ (t' : maximalIdeal A) (g' : Fin 2 → maximalIdeal A)
        (q' : MvPolynomial (Fin 3) (ResidueField A)),
      Ideal.span (Set.range fun i => (CaseOne.orderedGenerators t' g' i : A)) = maximalIdeal A ∧
      q' ≠ 0 ∧ q'.IsHomogeneous 2 ∧
      RingHom.ker (CaseOne.canonicalConeMap t' g') = Ideal.span {q'} ∧
      (MvPolynomial.eval₂Hom
        (MvPolynomial.C : ResidueField A →+* MvPolynomial (Fin 2) (ResidueField A))
        ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' ≠ 0) ∧
      (¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 2) (ResidueField A),
        L.IsHomogeneous 1 ∧ L ≠ 0 ∧
        MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0, MvPolynomial.X 1] q' =
          MvPolynomial.C c * L ^ 2) ∧
      x ∈ Set.range (CaseOneChart.chart B t') := by
  obtain ⟨i, hi⟩ := AffineAtlas.generator_covers (CaseOne.orderedGenerators t g)
    hgen (affineAtlas B) x
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 i
  let a : Fin 3 → maximalIdeal A := fun j => CaseOne.orderedGenerators t g (e j)
  let t' := a 0
  let g' := Fin.tail a
  let q' := MvPolynomial.rename e.symm q
  have hperm : CaseOne.orderedGenerators t' g' =
      fun j => CaseOne.orderedGenerators t g (e j) := Fin.cons_self_tail a
  have hgen' : Ideal.span (Set.range fun j =>
      (CaseOne.orderedGenerators t' g' j : A)) = maximalIdeal A := by
    have hr : Set.range (fun j => (CaseOne.orderedGenerators t' g' j : A)) =
        Set.range (fun j => (CaseOne.orderedGenerators t g j : A)) := by
      simp only [hperm]
      exact e.surjective.range_comp (fun j => (CaseOne.orderedGenerators t g j : A))
    rw [hr]
    exact hgen
  have hker' : RingHom.ker (CaseOne.canonicalConeMap t' g') = Ideal.span {q'} :=
    CaseOne.canonicalCone_kernel_permutation t t' g g' e hperm q hker
  have hq' : q'.IsHomogeneous 2 := MvPolynomial.IsHomogeneous.rename_isHomogeneous hq
  have hq'0 : q' ≠ 0 := by
    intro hz
    exact hq0 (MvPolynomial.rename_injective e.symm e.symm.injective
      (hz.trans (map_zero (MvPolynomial.rename e.symm)).symm))
  have ht' : (t' : A) ≠ 0 := CaseOne.denominator_ne_zero_of_kernel t' g' q' hq'0 hq' hker'
  have hQ0 : MvPolynomial.FirstCoordinate.dehom q' ≠ 0 := by
    intro hz
    apply hq'0
    apply MvPolynomial.FirstCoordinate.dehom_injective_on_homogeneous_two hq'
      (MvPolynomial.isHomogeneous_zero (Fin 3) (ResidueField A) 2)
    simpa only [map_zero] using hz
  have hdeg : (MvPolynomial.FirstCoordinate.dehom q').totalDegree ≤ 2 := by
    rw [GradedAlgebra.TernaryQuadratic.eq_quadratic_of_homogeneous hq']
    exact GradedAlgebra.TernaryQuadratic.dehom_quadratic_totalDegree _
  have hns' : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 3) (ResidueField A),
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q' = MvPolynomial.C c * L ^ 2 :=
    fun h => hns ((MvPolynomial.exists_scalar_homogeneous_square_rename_iff e.symm q 1).mp h)
  have hcase : ¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L : CaseOne.Plane A,
      L.totalDegree ≤ 1 ∧ MvPolynomial.FirstCoordinate.dehom q' = MvPolynomial.C c * L ^ 2 :=
    fun h => hns' ((MvPolynomial.FirstCoordinate.scalar_linear_square_iff hq' hq'0).mp h)
  have hchart : x ∈ Set.range (CaseOneChart.chart B t') := by
    have ht'eq : t' = CaseOne.orderedGenerators t g i :=
      congrArg (CaseOne.orderedGenerators t g) (Equiv.swap_apply_left 0 i)
    rw [ht'eq]
    exact hi
  let D' := CaseOne.presentationOfKernel t' g' hgen' q' hker'
  obtain ⟨M', hM', hQM', hpoint⟩ := CaseOneChart.exists_plane_point B D' x hx hbase hchart
  let _ : M'.IsMaximal := hM'
  have hs' : ¬ IsRegularLocalRing (B.Y.presheaf.stalk (CaseOneChart.point B D' M' hQM')) :=
    (congrArg (fun y : B.Y => ¬ IsRegularLocalRing (B.Y.presheaf.stalk y)) hpoint).mpr hsing
  obtain ⟨hr0, hrns⟩ := good_first_parameter_of_singular_stalk B hq' D' M' hQM'
    ht' hQ0 hdeg hcase hs'
  exact ⟨t', g', q', hgen', hq'0, hq', hker', hr0, hrns, hchart⟩

/-- Both-chart coverage removes the preferred-chart premise. The full
kernel and explicit nonreturn are obtained on the original stalk of x. -/
theorem exists_fixed_parameter_successor_at_closed_singular_point_of_hilbert
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
    (x : B.Y) (hx : IsClosed ({x} : Set B.Y)) (hbase : B.map x = closedPoint A)
    (hsing : ¬ IsRegularLocalRing (B.Y.presheaf.stalk x))
    (hHilbert : ∀ n, Module.finrank (ResidueField (B.Y.presheaf.stalk x))
      (Ideal.associatedGradedQuotientGrading (maximalIdeal (B.Y.presheaf.stalk x)) n) =
        2 * n + 1) :
    let S : Type u := B.Y.presheaf.stalk x
    let f : A →+* S := B.map.stalkScalar x
    let _ : IsLocalHom f := B.map.stalkScalar_isLocalHom_of_closedPoint x hbase
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
  have hchart := mem_parameterChart_of_closed_singular_point B t (g 0) (g 1)
    hgenPair q hq0 hq hkerPair hr0 hrns x hx hbase hsing
  obtain ⟨M', hM', hQM', hpoint⟩ := CaseOneChart.exists_plane_point B D' x hx hbase hchart
  let _ : M'.IsMaximal := hM'
  subst x
  exact exists_original_stalk_fixed_parameter_successor_of_hilbert B D' M' hQM'
    ht hQ0 hdeg hcase hsing hHilbert

end AlgebraicGeometry.Scheme.RationalDoublePoint.CaseOneNonreturn
