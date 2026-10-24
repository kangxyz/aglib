/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.DoubleLine.Marked.Chart

/-!
# Actual Case-II marked successors and local entry

The corrected marker persists through the original localized chart map.
The same fixed cubic determines the actual child and the two triple-entry
branches. Normal ordinary blowups and the genuine Case-II kernels retain
their stated geometric suppliers; no marked transition is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open Polynomial IsLocalRing

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- Evaluate a square-coordinate shift over one fixed local ring before
specializing its two coordinates to the native prime localization. -/
private theorem square_shift_value (w v t : maximalIdeal A) (μ V T : A)
    (h : w = v + μ • t) (hv : (v : A) = V) (ht : (t : A) = T) :
    (w : A) = V + μ * T := by
  rw [h, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, hv, ht]

end IsLocalRing

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

theorem marked_continuation_centered [IsNoetherianRing A]
    {t s z : maximalIdeal A} (D : ReducedDoubleLineChart t s z) (F : CubicRelation t s z)
    (h0 : F.coefficients.a0 = 0) (h1 : F.coefficients.a1 = 0) (h3 : F.coefficients.a3 = 0)
    (ha : residue A F.coefficients.a2 ≠ 0)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {X}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P) (D.centeredTriple P hP) =
      Ideal.span {L ^ 2}) :
    (∃ μ : Localization.AtPrime P, ∃ M : IsLocalRing.MarkedCubic (D.centeredTriple P hP 2),
      M.other = D.centeredTriple P hP 0 ∧
      M.square = D.centeredTriple P hP 1 + μ • D.centeredTriple P hP 2 ∧
      residue (Localization.AtPrime P) M.relation.coefficients.a2 =
        residue (Localization.AtPrime P)
          (localizedChartMap (maximalIdeal A) (t : A) P F.coefficients.a2)) ∧
    localizedChartMap (maximalIdeal A) (t : A) P (t : A) ∉
      maximalIdeal (Localization.AtPrime P) ^ 2 ∧
    (maximalIdeal A).map (localizedChartMap (maximalIdeal A) (t : A) P) =
      Ideal.span {localizedChartMap (maximalIdeal A) (t : A) P (t : A)} ∧
    ∃ hlocal : IsLocalHom (localizedChartMap (maximalIdeal A) (t : A) P),
      let _ := hlocal
      Function.Bijective (IsLocalRing.ResidueField.map (R := A) (S := Localization.AtPrime P)
        (localizedChartMap (maximalIdeal A) (t : A) P)) := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let B : Type u := Localization.AtPrime P
  let : IsNoetherianRing S := saturatedChart_isNoetherian (maximalIdeal A) (t : A)
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  let φ : A →+* S := algebraMap A S
  let loc : S →+* B := algebraMap S B
  let c : A →+* B := localizedChartMap (maximalIdeal A) (t : A) P
  let g := D.centeredTriple P hP
  let C := F.coefficients
  let τ := φ (t : A)
  let U := fractionElement (maximalIdeal A) t s
  let V := fractionElement (maximalIdeal A) t z
  let l := φ C.b0 + φ C.b1 * U + φ C.b2 * U ^ 2 +
    φ C.c0 * V + φ C.c1 * U * V + φ C.d0 * V ^ 2
  obtain ⟨r, hr⟩ := F.divided
  have hdiv : V ^ 2 + φ C.a2 * τ * U ^ 2 + τ * V * l + τ ^ 2 * r = 0 := by
    have h := hr
    change V ^ 2 + τ * (φ C.a0 + φ C.a1 * U + φ C.a2 * U ^ 2 + φ C.a3 * U ^ 3) +
      τ * V * l + τ ^ 2 * r = 0 at h
    change C.a0 = 0 at h0
    change C.a1 = 0 at h1
    change C.a3 = 0 at h3
    rw [h0, h1, h3, map_zero] at h
    linear_combination h
  have hg0 : (g 0 : B) = loc U := rfl
  have hg1 : (g 1 : B) = loc V := rfl
  have hg2 : (g 2 : B) = c (t : A) := rfl
  have hgen : maximalIdeal B = Ideal.span ({(g 2 : B), (g 0 : B), (g 1 : B)} : Set B) :=
    Ideal.localTriple_generates P τ U V (D.centered_prime_span P hP)
  have hrel : (g 1 : B) ^ 2 + c C.a2 * (g 2 : B) * (g 0 : B) ^ 2 +
      (g 2 : B) * (g 1 : B) * loc l + (g 2 : B) ^ 2 * loc r = 0 := by
    simpa only [hg0, hg1, hg2, c, localizedChartMap, RingHom.comp_apply,
      map_add, map_mul, map_pow, map_zero] using congrArg loc hdiv
  have hg : ![g 0, g 1, g 2] = g := by funext i; fin_cases i <;> rfl
  have hunit : IsUnit (c C.a2) := ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp ha).map c
  have hmarked := IsLocalRing.markedCubic_of_divided_relation (g 2) (g 0) (g 1)
    (c C.a2) (loc l) (loc r) hgen (hunit.map (residue B)).ne_zero hrel L hL
    (by rw [hg]; exact hCaseII)
  refine ⟨hmarked, ?_, localizedChartMap_center (maximalIdeal A) (t : A) t.property P,
    D.centered_residue_bijective P hP⟩
  exact IsLocalRing.first_not_mem_sq_of_span_triple_of_not_regular B
    (g 2 : B) (g 0 : B) (g 1 : B) hgen hd hsing

end Localization.Away.SaturatedChart

namespace IsLocalRing

open Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A]

theorem MarkedCubic.recenter_a2_residue {t : maximalIdeal A} (M : MarkedCubic t) (α : A) :
    residue A (M.recenter α).relation.coefficients.a2 = residue A M.relation.coefficients.a2 := by
  change residue A (M.relation.coefficients.substitute 1 0 α 1).a2 = _
  rw [CubicCoefficients.substitute_recenter_a2, map_add, map_mul, map_mul, map_ofNat,
    M.constant_at_infinity, mul_zero, zero_mul, add_zero]

end IsLocalRing

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The actual continuing child retains the SAME original parameter and the
original residue map. The repeated root and centered child kernel are derived. -/
theorem marked_continuation
    {t : maximalIdeal A} (M : IsLocalRing.MarkedCubic t)
    (D : ReducedDoubleLineChart t M.other M.square)
    (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (hq : Irreducible q) (hm : q.Monic)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) :
    ∃ α : A, ∃ μ : Localization.AtPrime P,
      ∃ N : IsLocalRing.MarkedCubic (D.primeTriple Q q hQ P hP 2),
        (N.other : Localization.AtPrime P) =
          algebraMap (saturatedChart A (maximalIdeal A) (t : A)) (Localization.AtPrime P)
            (fractionElement (maximalIdeal A) t (M.other - α • t)) ∧
        (N.square : Localization.AtPrime P) =
          algebraMap (saturatedChart A (maximalIdeal A) (t : A)) (Localization.AtPrime P)
            (fractionElement (maximalIdeal A) t M.square) +
          μ * localizedChartMap (maximalIdeal A) (t : A) P (t : A) ∧
        residue (Localization.AtPrime P) N.relation.coefficients.a2 =
          residue (Localization.AtPrime P)
            (localizedChartMap (maximalIdeal A) (t : A) P M.relation.coefficients.a2) ∧
        localizedChartMap (maximalIdeal A) (t : A) P (t : A) ∉
          maximalIdeal (Localization.AtPrime P) ^ 2 ∧
        (maximalIdeal A).map (localizedChartMap (maximalIdeal A) (t : A) P) =
          Ideal.span {localizedChartMap (maximalIdeal A) (t : A) P (t : A)} ∧
        ∃ hlocal : IsLocalHom (localizedChartMap (maximalIdeal A) (t : A) P),
          let _ := hlocal
          Function.Bijective (IsLocalRing.ResidueField.map (R := A) (S := Localization.AtPrime P)
            (localizedChartMap (maximalIdeal A) (t : A) P)) := by
  let B : Type u := Localization.AtPrime P
  let c : A →+* B := localizedChartMap (maximalIdeal A) (t : A) P
  have hs := D.child_sq_dvd M.relation Q q hQ P hP hd hsing L hL hCaseII
  have hn : M.relation.coefficients.residueCubic ≠ 0 := by
    intro hz
    apply M.linear_at_infinity
    rw [← CubicCoefficients.residueCubic_coeff_two, hz, Polynomial.coeff_zero]
  have hdeg : M.relation.coefficients.residueCubic.natDegree ≤ 3 :=
    IsLocalRing.residueBinaryCubic_natDegree_le _ _ _ _
  obtain ⟨a, hqa⟩ := Polynomial.exists_eq_X_sub_C_of_monic_irreducible_sq_dvd_cubic
    hn hdeg hq hm hs
  obtain ⟨α, hα⟩ := residue_surjective (R := A) a
  have hqα : q = X - Polynomial.C (residue A α) := by rw [hα]; exact hqa
  have hP0 : P = (Ideal.span {X}).comap (D.recenter α).map := by
    rw [D.recenter_prime]
    simpa only [hqα] using hP
  obtain ⟨L', hL', hker'⟩ :=
    D.centered_kernel_of_linear_prime Q q hQ P hP α hqα hP0 L hL hCaseII
  let M0 := M.recenter α
  have hz := M.relation.recenter_zero_coefficients α (by simpa only [hqα] using hs)
  have hM0 : M0.relation.coefficients = (M.relation.recenter α).coefficients := rfl
  have hz0 : residue A M0.relation.coefficients.a0 = 0 := by rw [hM0]; exact hz.1
  have hz1 : residue A M0.relation.coefficients.a1 = 0 := by rw [hM0]; exact hz.2
  let F0 := M0.relation.replacePure 0 0 M0.relation.coefficients.a2 0
    (by simpa only [map_zero] using hz0)
    (by simpa only [map_zero] using hz1) rfl
    (by simpa only [map_zero] using M0.constant_at_infinity)
  have hF0a2 : F0.coefficients.a2 = (M.recenter α).relation.coefficients.a2 := rfl
  obtain ⟨hmarked, hminimal, hcenter, hres⟩ := marked_continuation_centered
    (D.recenter α) F0 rfl rfl rfl M0.linear_at_infinity P hP0 hd hsing L' hL' hker'
  obtain ⟨μ, N, hNu, hNw, hNa⟩ := hmarked
  obtain ⟨hlocal, hbij⟩ := hres
  let _ := hlocal
  have hcoeff : residue B (c F0.coefficients.a2) =
      residue B (c M.relation.coefficients.a2) := by
    rw [hF0a2]
    have h := congrArg (IsLocalRing.ResidueField.map (R := A) (S := B) c)
      (M.recenter_a2_residue α)
    simpa only [IsLocalRing.ResidueField.map_residue] using h
  refine ⟨α, μ, N, ?_, ?_, hNa.trans hcoeff, hminimal, hcenter, hlocal, hbij⟩
  · exact congrArg Subtype.val hNu
  · exact IsLocalRing.square_shift_value N.square
      ((D.recenter α).centeredTriple P hP0 1)
      ((D.recenter α).centeredTriple P hP0 2) μ _ _ hNw rfl rfl

end Localization.Away.SaturatedChart

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- A continuing Case-II point in the opposite chart lies in the overlap with
the marker chart. The missing point is excluded using the same original cubic. -/
theorem marked_opposite_parameter_not_mem
    {t : maximalIdeal A} (M : IsLocalRing.MarkedCubic t)
    (D : ReducedDoubleLineChart M.other t M.square)
    (Q : saturatedChart A (maximalIdeal A) (M.other : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (hq : Irreducible q) (hm : q.Monic)
    (P : Ideal (saturatedChart A (maximalIdeal A) (M.other : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) :
    fractionElement (maximalIdeal A) M.other t ∉ P := by
  intro hmem
  have hx : (X : (IsLocalRing.ResidueField A)[X]) ∈ Ideal.span {q} := by
    rw [hP] at hmem
    change D.map (fractionElement (maximalIdeal A) M.other t) ∈ Ideal.span {q} at hmem
    rwa [D.other] at hmem
  have hqX : q = X := Polynomial.eq_of_monic_of_associated hm Polynomial.monic_X
    (hq.associated_of_dvd Polynomial.irreducible_X (Ideal.mem_span_singleton.mp hx))
  have hdiv := D.child_sq_dvd M.relation.swap Q q hQ P hP hd hsing L hL hCaseII
  rw [hqX] at hdiv
  have hlinear := Polynomial.X_pow_dvd_iff.mp hdiv 1 (by decide)
  apply M.linear_at_infinity
  change (M.relation.coefficients.swap.residueCubic).coeff 1 = 0 at hlinear
  simpa only [CubicCoefficients.residueCubic_coeff_one, CubicCoefficients.swap] using hlinear

end Localization.Away.SaturatedChart

namespace RingHom

variable {S B : Type u} [Semiring S] [Semiring B]

private theorem map_first_entry_relation (f : S →+* B) (t u v a l r : S)
    (h : v ^ 2 + a * t * u ^ 3 + t * v * l + t ^ 2 * r = 0) :
    (f v) ^ 2 + f a * f t * (f u) ^ 3 + f t * f v * f l +
      (f t) ^ 2 * f r = 0 := by
  simpa only [map_add, map_mul, map_pow, map_zero] using congrArg f h

private theorem map_second_entry_relation (f : S →+* B)
    (t r v b p q alpha gamma : S)
    (h : v ^ 2 + b * t ^ 2 * r + t * r * v * p +
      t * r ^ 2 * (alpha * r + gamma * v) + t ^ 2 * r ^ 2 * q = 0) :
    (f v) ^ 2 + f b * (f t) ^ 2 * f r + f t * f r * f v * f p +
      f t * (f r) ^ 2 * (f alpha * f r + f gamma * f v) +
      (f t) ^ 2 * (f r) ^ 2 * f q = 0 := by
  simpa only [map_add, map_mul, map_pow, map_zero] using congrArg f h

end RingHom

namespace Ideal

variable {S : Type u} [CommRing S] [IsNoetherianRing S]

/-- Perform the entire first-entry construction in the native prime
localization of a variable source ring, with its original scalar map. -/
private theorem localTriple_first_entry
    (P : Ideal S) [P.IsPrime] (t u v a l r : S)
    (hP : P = Ideal.span ({t, u, v} : Set S)) (ha : IsUnit a)
    (hrel : v ^ 2 + a * t * u ^ 3 + t * v * l + t ^ 2 * r = 0)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hker : IsLocalRing.doubleLineChildCotangentKernel (Localization.AtPrime P)
      (localTriple P t u v hP) = Ideal.span {L ^ 2})
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P)) :
    let g := localTriple P t u v hP
    ∃ μ : Localization.AtPrime P,
      ∃ T : IsLocalRing.TripleEntryData (g 2) (g 0) (g 1 + μ • g 2),
        T.coefficient = algebraMap S (Localization.AtPrime P) a ∧
        algebraMap S (Localization.AtPrime P) t ∉ maximalIdeal (Localization.AtPrime P) ^ 2 := by
  let B : Type u := Localization.AtPrime P
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  let loc : S →+* B := algebraMap S B
  let g := localTriple P t u v hP
  have hg0 : (g 0 : B) = loc u := rfl
  have hg1 : (g 1 : B) = loc v := rfl
  have hg2 : (g 2 : B) = loc t := rfl
  have hgen : maximalIdeal B = Ideal.span ({(g 2 : B), (g 0 : B), (g 1 : B)} : Set B) :=
    localTriple_generates P t u v hP
  have hrelB : (g 1 : B) ^ 2 + loc a * (g 2 : B) * (g 0 : B) ^ 3 +
      (g 2 : B) * (g 1 : B) * loc l + (g 2 : B) ^ 2 * loc r = 0 := by
    rw [hg0, hg1, hg2]
    exact RingHom.map_first_entry_relation loc t u v a l r hrel
  have hg : ![g 0, g 1, g 2] = g := by funext i; fin_cases i <;> rfl
  obtain ⟨μ, T, hT⟩ := IsLocalRing.exists_tripleEntryData_of_divided_relation
    (g 2) (g 0) (g 1) (loc a) (loc l) (loc r) (ha.map loc) hgen hrelB L hL
    (by rw [hg]; exact hker)
  refine ⟨μ, T, hT, ?_⟩
  exact IsLocalRing.first_not_mem_sq_of_span_triple_of_not_regular B
    (g 2 : B) (g 0 : B) (g 1 : B) hgen hd hsing

/-- Transport the retained second-chart identity, its full kernel and its
marker through the same native localization before the chart is specialized. -/
private theorem localTriple_second_entry
    (P : Ideal S) [P.IsPrime] (t r v b p q alpha gamma : S)
    (hP : P = Ideal.span ({t, r, v} : Set S)) (hb : IsUnit b)
    (hrel : v ^ 2 + b * t ^ 2 * r + t * r * v * p +
      t * r ^ 2 * (alpha * r + gamma * v) + t ^ 2 * r ^ 2 * q = 0)
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hker : IsLocalRing.doubleLineChildCotangentKernel (Localization.AtPrime P)
      (localTriple P t r v hP) = Ideal.span {L ^ 2})
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P)) :
    let g := localTriple P t r v hP
    (∃ M : IsLocalRing.MarkedCubic (g 0), M.other = g 2 ∧ M.square = g 1 ∧
      residue (Localization.AtPrime P) M.relation.coefficients.a2 =
        residue (Localization.AtPrime P) (algebraMap S (Localization.AtPrime P) b)) ∧
    (g 0 : Localization.AtPrime P) ∉ maximalIdeal (Localization.AtPrime P) ^ 2 := by
  let B : Type u := Localization.AtPrime P
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  let loc : S →+* B := algebraMap S B
  let g := localTriple P t r v hP
  have hg0 : (g 0 : B) = loc r := rfl
  have hg1 : (g 1 : B) = loc v := rfl
  have hg2 : (g 2 : B) = loc t := rfl
  have hrelB : (g 1 : B) ^ 2 + loc b * (g 2 : B) ^ 2 * (g 0 : B) +
      (g 2 : B) * (g 0 : B) * (g 1 : B) * loc p +
      (g 2 : B) * (g 0 : B) ^ 2 * (loc alpha * (g 0 : B) + loc gamma * (g 1 : B)) +
      (g 2 : B) ^ 2 * (g 0 : B) ^ 2 * loc q = 0 := by
    rw [hg0, hg1, hg2]
    exact RingHom.map_second_entry_relation loc t r v b p q alpha gamma hrel
  have hgen0 : maximalIdeal B = Ideal.span ({(g 2 : B), (g 0 : B), (g 1 : B)} : Set B) :=
    localTriple_generates P t r v hP
  have hgen : maximalIdeal B = Ideal.span ({(g 0 : B), (g 2 : B), (g 1 : B)} : Set B) := by
    simpa only [Set.insert_comm] using hgen0
  obtain ⟨L', hL', hkernel⟩ := IsLocalRing.cotangentKernel_swapPlane g L hL hker
  have hmarked := IsLocalRing.markedCubic_of_second_triple_equation
    (g 0) (g 2) (g 1) (loc b) (loc p) (loc q) (loc alpha) (loc gamma)
    (hb.map loc) hgen hrelB L' hL' hkernel
  refine ⟨hmarked, ?_⟩
  exact IsLocalRing.first_not_mem_sq_of_span_triple_of_not_regular B
    (g 0 : B) (g 2 : B) (g 1 : B) hgen hd hsing

end Ideal

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The first literal chart at a triple root produces its exact aligned triple
identity and retains the original coefficient and original residue map. -/
theorem triple_entry_centered
    {t s z : maximalIdeal A} (D : ReducedDoubleLineChart t s z) (F : CubicRelation t s z)
    (h0 : F.coefficients.a0 = 0) (h1 : F.coefficients.a1 = 0) (h2 : F.coefficients.a2 = 0)
    (ha : residue A F.coefficients.a3 ≠ 0)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {X}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P) (D.centeredTriple P hP) =
      Ideal.span {L ^ 2}) :
    ∃ μ : Localization.AtPrime P,
      ∃ T : IsLocalRing.TripleEntryData (D.centeredTriple P hP 2) (D.centeredTriple P hP 0)
        (D.centeredTriple P hP 1 + μ • D.centeredTriple P hP 2),
        T.coefficient = localizedChartMap (maximalIdeal A) (t : A) P F.coefficients.a3 ∧
        localizedChartMap (maximalIdeal A) (t : A) P (t : A) ∉
          maximalIdeal (Localization.AtPrime P) ^ 2 ∧
        (maximalIdeal A).map (localizedChartMap (maximalIdeal A) (t : A) P) =
          Ideal.span {localizedChartMap (maximalIdeal A) (t : A) P (t : A)} ∧
        ∃ hlocal : IsLocalHom (localizedChartMap (maximalIdeal A) (t : A) P),
          let _ := hlocal
          Function.Bijective (IsLocalRing.ResidueField.map (R := A) (S := Localization.AtPrime P)
            (localizedChartMap (maximalIdeal A) (t : A) P)) := by
  let S : Type u := saturatedChart A (maximalIdeal A) (t : A)
  let : IsNoetherianRing S := saturatedChart_isNoetherian (maximalIdeal A) (t : A)
  let φ : A →+* S := algebraMap A S
  let C := F.coefficients
  let τ := φ (t : A)
  let U := fractionElement (maximalIdeal A) t s
  let V := fractionElement (maximalIdeal A) t z
  let l := φ C.b0 + φ C.b1 * U + φ C.b2 * U ^ 2 +
    φ C.c0 * V + φ C.c1 * U * V + φ C.d0 * V ^ 2
  obtain ⟨r, hr⟩ := F.divided
  have hdiv : V ^ 2 + φ C.a3 * τ * U ^ 3 + τ * V * l + τ ^ 2 * r = 0 := by
    have h := hr
    change V ^ 2 + τ * (φ C.a0 + φ C.a1 * U + φ C.a2 * U ^ 2 + φ C.a3 * U ^ 3) +
      τ * V * l + τ ^ 2 * r = 0 at h
    change C.a0 = 0 at h0
    change C.a1 = 0 at h1
    change C.a2 = 0 at h2
    rw [h0, h1, h2, map_zero] at h
    linear_combination h
  have hunit : IsUnit (φ C.a3) :=
    ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp ha).map φ
  obtain ⟨μ, T, hT, hminimal⟩ := Ideal.localTriple_first_entry P τ U V (φ C.a3) l r
    (D.centered_prime_span P hP) hunit hdiv L hL hCaseII hd hsing
  exact ⟨μ, T, hT, hminimal,
    localizedChartMap_center (maximalIdeal A) (t : A) t.property P,
    D.centered_residue_bijective P hP⟩

/-- At the actual centered second child, the retained triple equation produces
its new marker `t/u` and the original residue-map bijection. -/
theorem triple_second_entry_centered
    {t u w : maximalIdeal A} (T : IsLocalRing.TripleEntryData t u w)
    (D : ReducedDoubleLineChart u t w)
    (alpha gamma Q2 : A) (hQ2 : Q2 ∈ maximalIdeal A ^ 2)
    (hQ : T.Q = alpha * (t : A) + gamma * (w : A) + Q2)
    (P : Ideal (saturatedChart A (maximalIdeal A) (u : A))) [P.IsPrime]
    (hP : P = (Ideal.span {X}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P) (D.centeredTriple P hP) =
      Ideal.span {L ^ 2}) :
    (∃ M : IsLocalRing.MarkedCubic (D.centeredTriple P hP 0),
      M.other = D.centeredTriple P hP 2 ∧ M.square = D.centeredTriple P hP 1 ∧
      residue (Localization.AtPrime P) M.relation.coefficients.a2 =
        residue (Localization.AtPrime P)
          (localizedChartMap (maximalIdeal A) (u : A) P T.coefficient)) ∧
    (D.centeredTriple P hP 0 : Localization.AtPrime P) ∉
      maximalIdeal (Localization.AtPrime P) ^ 2 ∧
    ∃ hlocal : IsLocalHom (localizedChartMap (maximalIdeal A) (u : A) P),
      let _ := hlocal
      Function.Bijective (IsLocalRing.ResidueField.map (R := A) (S := Localization.AtPrime P)
        (localizedChartMap (maximalIdeal A) (u : A) P)) := by
  let S : Type u := saturatedChart A (maximalIdeal A) (u : A)
  let : IsNoetherianRing S := saturatedChart_isNoetherian (maximalIdeal A) (u : A)
  let φ : A →+* S := algebraMap A S
  obtain ⟨P1, Q2', heq⟩ := TripleEntryData_second_chart_equation T alpha gamma Q2 hQ2 hQ
  have hentry := Ideal.localTriple_second_entry P (φ (u : A))
    (fractionElement (maximalIdeal A) u t) (fractionElement (maximalIdeal A) u w)
    (φ T.coefficient) P1 Q2' (φ alpha) (φ gamma) (D.centered_prime_span P hP)
    (T.coefficient_unit.map φ) heq L hL hCaseII hd hsing
  exact ⟨hentry.1, hentry.2, D.centered_residue_bijective P hP⟩

end Localization.Away.SaturatedChart

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- A fixed cubic of degree at most one in this chart has no continuing
Case-II child. Its nonvanishing must come from the genuine normal blowup input. -/
theorem no_child_of_linear_cubic
    {t s z : maximalIdeal A} (D : ReducedDoubleLineChart t s z) (F : CubicRelation t s z)
    (h2 : F.coefficients.a2 = 0) (h3 : F.coefficients.a3 = 0)
    (hn : F.coefficients.residueCubic ≠ 0)
    (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q) (hq : Irreducible q)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) : False := by
  have hdiv := D.child_sq_dvd F Q q hQ P hP hd hsing L hL hCaseII
  have heq : F.coefficients.residueCubic =
      C (residue A F.coefficients.a0) + C (residue A F.coefficients.a1) * X := by
    dsimp only [CubicCoefficients.residueCubic, IsLocalRing.residueBinaryCubic]
    simp only [h2, h3, map_zero, zero_mul, add_zero, zero_add]
    exact add_comm _ _
  have hdeg : F.coefficients.residueCubic.natDegree ≤ 1 := by
    rw [heq]
    exact Polynomial.natDegree_add_le_of_degree_le (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le)
  have hb := (Polynomial.natDegree_le_of_dvd hdiv hn).trans hdeg
  rw [Polynomial.natDegree_pow] at hb
  have hp := hq.natDegree_pos
  omega

/-- A genuine continuing child of a normalized triple root is the actual
origin, and its exact triple identity is produced without a point premise. -/
theorem triple_entry
    {t s z : maximalIdeal A} (D : ReducedDoubleLineChart t s z) (F : CubicRelation t s z)
    (h0 : F.coefficients.a0 = 0) (h1 : F.coefficients.a1 = 0) (h2 : F.coefficients.a2 = 0)
    (ha : residue A F.coefficients.a3 ≠ 0)
    (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (hq : Irreducible q) (hm : q.Monic)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) :
    q = X ∧ ∃ hP0 : P = (Ideal.span {X}).comap D.map,
      ∃ μ : Localization.AtPrime P,
        ∃ T : IsLocalRing.TripleEntryData (D.centeredTriple P hP0 2) (D.centeredTriple P hP0 0)
          (D.centeredTriple P hP0 1 + μ • D.centeredTriple P hP0 2),
          T.coefficient = localizedChartMap (maximalIdeal A) (t : A) P F.coefficients.a3 ∧
          localizedChartMap (maximalIdeal A) (t : A) P (t : A) ∉
            maximalIdeal (Localization.AtPrime P) ^ 2 ∧
          (maximalIdeal A).map (localizedChartMap (maximalIdeal A) (t : A) P) =
            Ideal.span {localizedChartMap (maximalIdeal A) (t : A) P (t : A)} ∧
          ∃ hlocal : IsLocalHom (localizedChartMap (maximalIdeal A) (t : A) P),
            let _ := hlocal
            Function.Bijective (IsLocalRing.ResidueField.map (R := A) (S := Localization.AtPrime P)
              (localizedChartMap (maximalIdeal A) (t : A) P)) := by
  have hn : F.coefficients.residueCubic ≠ 0 := by
    intro hz
    apply ha
    rw [← CubicCoefficients.residueCubic_coeff_three, hz, Polynomial.coeff_zero]
  have hqX := D.prime_eq_X_of_zero_low_coefficients F
    (by rw [h0, map_zero]) (by rw [h1, map_zero]) hn Q q hQ hq hm P hP hd hsing L hL hCaseII
  have hP0 : P = (Ideal.span {X}).comap D.map := by simpa only [hqX] using hP
  obtain ⟨L', hL', hkernel⟩ :=
    D.centered_kernel_of_origin Q q hQ hqX P hP hP0 L hL hCaseII
  exact ⟨hqX, hP0, triple_entry_centered D F h0 h1 h2 ha P hP0 hd hsing L' hL' hkernel⟩

/-- A triple-entry stage is marked at that stage or at its next actual
continuing child. The fixed first-child cubic is nonzero by the supplied
normal ordinary blowup, and the actual second point is derived. -/
theorem triple_entry_next [IsDomain A]
    {t u w : maximalIdeal A} (T : IsLocalRing.TripleEntryData t u w)
    (ht0 : (t : A) ≠ 0)
    [IsIntegrallyClosed (saturatedChart A (maximalIdeal A) (t : A))]
    (D : ReducedDoubleLineChart u t w)
    (Q : saturatedChart A (maximalIdeal A) (u : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (hq : Irreducible q) (hm : q.Monic)
    (P : Ideal (saturatedChart A (maximalIdeal A) (u : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) :
    (∃ r : maximalIdeal A, ∃ M : IsLocalRing.MarkedCubic r, M.other = t ∧ M.square = w) ∨
      (q = X ∧ ∃ hP0 : P = (Ideal.span {X}).comap D.map,
        (∃ M : IsLocalRing.MarkedCubic (D.centeredTriple P hP0 0),
          M.other = D.centeredTriple P hP0 2 ∧ M.square = D.centeredTriple P hP0 1 ∧
          residue (Localization.AtPrime P) M.relation.coefficients.a2 =
            residue (Localization.AtPrime P)
              (localizedChartMap (maximalIdeal A) (u : A) P T.coefficient)) ∧
        (D.centeredTriple P hP0 0 : Localization.AtPrime P) ∉
          maximalIdeal (Localization.AtPrime P) ^ 2 ∧
        ∃ hlocal : IsLocalHom (localizedChartMap (maximalIdeal A) (u : A) P),
          let _ := hlocal
          Function.Bijective (IsLocalRing.ResidueField.map (R := A) (S := Localization.AtPrime P)
            (localizedChartMap (maximalIdeal A) (u : A) P))) := by
  obtain ⟨alpha, beta, gamma, F, hQsplit, hF0, hF1, hF2, hF3, _⟩ := T.exists_fixed_cubic
  by_cases hbeta : residue A beta = 0
  · right
    have hn := fixed_cubic_nonzero ht0 T.presentation F
    have halpha : residue A alpha ≠ 0 := by
      intro ha
      apply hn
      dsimp only [CubicCoefficients.residueCubic, IsLocalRing.residueBinaryCubic]
      simp only [hF0, hF1, hF2, hF3, ha, hbeta, map_zero, zero_mul, add_zero]
    have hn' : F.swap.coefficients.residueCubic ≠ 0 := by
      intro hz
      apply halpha
      have h := congrArg (fun p : (IsLocalRing.ResidueField A)[X] => p.coeff 3) hz
      simpa only [CubicCoefficients.residueCubic_coeff_three, Polynomial.coeff_zero,
        CubicRelation.swap, CubicCoefficients.swap, hF0] using h
    have hqX := D.prime_eq_X_of_zero_low_coefficients F.swap
      (by change residue A F.coefficients.a3 = 0; rw [hF3, map_zero])
      (by change residue A F.coefficients.a2 = 0; rw [hF2, map_zero])
      hn' Q q hQ hq hm P hP hd hsing L hL hCaseII
    have hP0 : P = (Ideal.span {X}).comap D.map := by simpa only [hqX] using hP
    obtain ⟨L', hL', hkernel⟩ :=
      D.centered_kernel_of_origin Q q hQ hqX P hP hP0 L hL hCaseII
    obtain ⟨Q2, hQ2, hQ2eq⟩ := T.split_Q_of_beta_zero alpha beta gamma hQsplit hbeta
    exact ⟨hqX, hP0, triple_second_entry_centered T D alpha gamma Q2 hQ2 hQ2eq
      P hP0 hd hsing L' hL' hkernel⟩
  · left
    obtain ⟨M, hMt, hMw⟩ := T.marked_of_beta_nonzero alpha beta F hF0 hF1 hF2 hF3 hbeta
    exact ⟨beta • u + alpha • t, M, hMt, hMw⟩

end Localization.Away.SaturatedChart

namespace Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- An arbitrary actual Case-II child supplies either an original-ring marker,
or the first triple-entry identity. The rational repeated point, low
coefficient vanishing, coordinate transport, and original residue bijection
are conclusions for the actual chart. -/
theorem entry_reduction
    {t s z : maximalIdeal A} (D : ReducedDoubleLineChart t s z) (F : CubicRelation t s z)
    (hgen : maximalIdeal A = Ideal.span ({(t : A), (s : A), (z : A)} : Set A))
    (hker : doubleLineChildCotangentKernel A ![s, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2})
    (hn : F.coefficients.residueCubic ≠ 0)
    (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X]) (hQ : D.map Q = q)
    (hq : Irreducible q) (hm : q.Monic)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap D.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (D.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) :
    (∃ r : maximalIdeal A, ∃ M : IsLocalRing.MarkedCubic r, M.square = z) ∨
      (∃ α : A, ∃ hP0 : P = (Ideal.span {X}).comap (D.recenter α).map,
        ∃ μ : Localization.AtPrime P,
          ∃ T : IsLocalRing.TripleEntryData ((D.recenter α).centeredTriple P hP0 2)
            ((D.recenter α).centeredTriple P hP0 0)
            ((D.recenter α).centeredTriple P hP0 1 +
              μ • (D.recenter α).centeredTriple P hP0 2),
            T.coefficient = localizedChartMap (maximalIdeal A) (t : A) P F.coefficients.a3 ∧
            localizedChartMap (maximalIdeal A) (t : A) P (t : A) ∉
              maximalIdeal (Localization.AtPrime P) ^ 2 ∧
            (maximalIdeal A).map (localizedChartMap (maximalIdeal A) (t : A) P) =
              Ideal.span {localizedChartMap (maximalIdeal A) (t : A) P (t : A)} ∧
            ∃ hlocal : IsLocalHom (localizedChartMap (maximalIdeal A) (t : A) P),
              let _ := hlocal
              Function.Bijective
                (IsLocalRing.ResidueField.map (R := A) (S := Localization.AtPrime P)
                  (localizedChartMap (maximalIdeal A) (t : A) P))) := by
  have hsq := D.child_sq_dvd F Q q hQ P hP hd hsing L hL hCaseII
  obtain ⟨a, hqa⟩ := Polynomial.exists_eq_X_sub_C_of_monic_irreducible_sq_dvd_cubic
    hn (IsLocalRing.residueBinaryCubic_natDegree_le _ _ _ _) hq hm hsq
  obtain ⟨α, hα⟩ := residue_surjective (R := A) a
  have hqα : q = X - C (residue A α) := by rw [hα]; exact hqa
  have hP0 : P = (Ideal.span {X}).comap (D.recenter α).map := by
    rw [D.recenter_prime]
    simpa only [hqα] using hP
  obtain ⟨L', hL', hkernel⟩ :=
    D.centered_kernel_of_linear_prime Q q hQ P hP α hqα hP0 L hL hCaseII
  let s0 := s - α • t
  let F0 := F.recenter α
  have hz := F.recenter_zero_coefficients α (by simpa only [hqα] using hsq)
  have hz0 : residue A F0.coefficients.a0 = 0 := hz.1
  have hz1 : residue A F0.coefficients.a1 = 0 := hz.2
  have hn0 : F0.coefficients.residueCubic ≠ 0 := by
    change (F.coefficients.substitute 1 0 α 1).residueCubic ≠ 0
    rw [CubicCoefficients.residueCubic_recenter]
    exact Polynomial.comp_X_add_C_ne_zero_iff.mpr hn
  have hgen0 : maximalIdeal A = Ideal.span ({(t : A), (s0 : A), (z : A)} : Set A) := by
    have hs0 : (s0 : A) = (s : A) - α * (t : A) := by
      simp only [s0, Submodule.coe_sub, Submodule.coe_smul, smul_eq_mul]
    rw [hs0]
    have h := IsLocalRing.maximalIdeal_planeChange t s z 1 (-α) 0 1 (by simp) hgen
    simpa only [one_mul, zero_mul, zero_add, add_zero, sub_eq_add_neg, neg_mul] using h
  have hker0 : doubleLineChildCotangentKernel A ![s0, z, t] =
      Ideal.span {(MvPolynomial.X 1 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField A)) ^ 2} := by
    have h := IsLocalRing.cotangentKernel_planeChange ![s, z, t] 1 (-α) 0 1 (by simp) hker
    simpa only [s0, IsLocalRing.planeChangeTriple_triple, one_smul, zero_smul,
      zero_add, add_zero, neg_smul, sub_eq_add_neg] using h
  let F1 := F0.replacePure 0 0 F0.coefficients.a2 F0.coefficients.a3
    (by simpa only [map_zero] using hz0)
    (by simpa only [map_zero] using hz1) rfl rfl
  have hF1a2 : F1.coefficients.a2 = F0.coefficients.a2 := rfl
  by_cases ha2 : residue A F0.coefficients.a2 = 0
  · right
    have ha3 : residue A F0.coefficients.a3 ≠ 0 := by
      intro ha3
      apply hn0
      dsimp only [CubicCoefficients.residueCubic, IsLocalRing.residueBinaryCubic]
      simp only [hz0, hz1, ha2, ha3, map_zero, zero_mul, add_zero]
    let F2 := F1.replacePure 0 0 0 F1.coefficients.a3 rfl rfl
      (by rw [hF1a2, map_zero]; exact ha2) rfl
    have hF2a3 : F2.coefficients.a3 = F0.coefficients.a3 := rfl
    obtain ⟨μ, T, hT, hmin, hcenter, hres⟩ := triple_entry_centered (D.recenter α) F2
      rfl rfl rfl (by rwa [hF2a3]) P hP0 hd hsing L' hL' hkernel
    have h3 : F2.coefficients.a3 = F.coefficients.a3 := hF2a3.trans
      (CubicCoefficients.substitute_recenter_a3 F.coefficients α)
    exact ⟨α, hP0, μ, T, hT.trans (congrArg _ h3), hmin, hcenter, hres⟩
  · left
    obtain ⟨M, _, hMz⟩ := IsLocalRing.markedCubic_of_simple_factor
      t s0 z F1 hgen0 hker0 rfl rfl (by rwa [hF1a2])
    exact ⟨_, M, hMz⟩

end Localization.Away.SaturatedChart

namespace IsLocalRing.TripleEntryData

open Localization.Away Localization.Away.SaturatedChart

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
variable {t u w : maximalIdeal A} (T : TripleEntryData t u w)

/-- No continuing child of the aligned triple stage lies on its old parameter
chart. Its nonzero linear cubic is the fixed cubic of the same exact equation. -/
theorem no_continuing_parameter_chart
    (ht0 : (t : A) ≠ 0)
    [IsIntegrallyClosed (saturatedChart A (maximalIdeal A) (t : A))]
    (Q : saturatedChart A (maximalIdeal A) (t : A))
    (q : (IsLocalRing.ResidueField A)[X])
    (hQ : T.presentation.reducedChart.map Q = q) (hq : Irreducible q)
    (P : Ideal (saturatedChart A (maximalIdeal A) (t : A))) [P.IsPrime]
    (hP : P = (Ideal.span {q}).comap T.presentation.reducedChart.map)
    (hd : ringKrullDim (Localization.AtPrime P) = 2)
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime P))
    (L : MvPolynomial (Fin 3) (IsLocalRing.ResidueField (Localization.AtPrime P)))
    (hL : L.IsHomogeneous 1)
    (hCaseII : doubleLineChildCotangentKernel (Localization.AtPrime P)
      (T.presentation.reducedChart.primeTriple Q q hQ P hP) = Ideal.span {L ^ 2}) : False := by
  obtain ⟨_, _, _, F, _, _, _, hF2, hF3, _⟩ := T.exists_fixed_cubic
  exact no_child_of_linear_cubic T.presentation.reducedChart F hF2 hF3
    (fixed_cubic_nonzero ht0 T.presentation F) Q q hQ hq P hP hd hsing L hL hCaseII

end IsLocalRing.TripleEntryData

