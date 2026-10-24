/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.PurelyInseparable.FiniteConstantRoots
public import Aglib.RingTheory.IntegralClosure.NormalHull
public import Aglib.RingTheory.Nagata.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomial rings over Japanese domains

The purely inseparable case uses finite constant roots inside an actual
algebraic closure. The normal model is the polynomial ring over the literal
coefficient normalization, with the original variable acting by a positive
power of its variable. Bounded powers give a finite module. The general case
uses the finite normal-hull reduction, without a normality hypothesis on the
original coefficient ring.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace IsJapaneseRing

private theorem finite_polynomial_of_power
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Algebra R[X] A[X]]
    (q : ℕ) (hq : 0 < q)
    (hC : ∀ r, algebraMap R[X] A[X] (C r) = C (algebraMap R A r))
    (hX : algebraMap R[X] A[X] X = X ^ q) :
    Module.Finite R[X] A[X] := by
  classical
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := R) (M := A)
  let g : Fin n × Fin q → A[X] := fun j => C (b j.1) * X ^ (j.2 : ℕ)
  let M := Submodule.span R[X] (Set.range g)
  have hmon (m : ℕ) (a : A) : C a * X ^ m ∈ M := by
    have ha : a ∈ Submodule.span R (Set.range b) := by rw [hb]; trivial
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      have hg : C (b j) * X ^ (m % q) ∈ M :=
        Submodule.subset_span ⟨(j, ⟨m % q, Nat.mod_lt m hq⟩), rfl⟩
      have hs := M.smul_mem (X ^ (m / q) : R[X]) hg
      have heq : (X ^ (m / q) : R[X]) • (C (b j) * X ^ (m % q)) =
          C (b j) * X ^ m := by
        rw [Algebra.smul_def, map_pow, hX, ← pow_mul]
        calc
          X ^ (q * (m / q)) * (C (b j) * X ^ (m % q)) =
              C (b j) * (X ^ (m % q) * X ^ (q * (m / q))) := by ring
          _ = C (b j) * X ^ m := by rw [← pow_add, Nat.mod_add_div]
      exact heq ▸ hs
    | zero => simp only [map_zero, zero_mul, M.zero_mem]
    | add a c _ _ ha hc =>
      simpa only [map_add, add_mul] using M.add_mem ha hc
    | smul r a _ ha =>
      have hs := M.smul_mem (C r : R[X]) ha
      simpa only [Algebra.smul_def, hC, map_mul, mul_assoc] using hs
  have hM : M = ⊤ := by
    apply top_le_iff.mp
    intro a ha
    clear ha
    induction a using Polynomial.induction_on' with
    | add a b ha hb => exact M.add_mem ha hb
    | monomial m c => simpa only [C_mul_X_pow_eq_monomial] using hmon m c
  apply Module.Finite.of_fg_top
  rw [← hM]
  exact Submodule.fg_span (Set.finite_range g)

private theorem isFractionRing_polynomial_of_rational_presentation
    (A K S : Type*) [CommRing A] [IsDomain A] [Field K] [Field S]
    [Algebra A K] [IsFractionRing A K] [Algebra A S] [Algebra K S]
    [IsScalarTower A K S] [Algebra A[X] S] [IsScalarTower A A[X] S]
    (z : S) (hX : algebraMap A[X] S X = z)
    (hinj : Function.Injective (algebraMap A[X] S))
    (hS : ∀ x : S, ∃ a b : K[X], x = aeval z a / aeval z b) :
    IsFractionRing A[X] S := by
  let f : FractionRing A[X] →+* S := IsFractionRing.lift hinj
  have hcoeff (a : A) : algebraMap A S a ∈ f.fieldRange := by
    refine ⟨algebraMap A[X] (FractionRing A[X]) (C a), ?_⟩
    rw [IsFractionRing.lift_algebraMap]
    exact (IsScalarTower.algebraMap_apply A A[X] S a).symm
  have hK (a : K) : algebraMap K S a ∈ f.fieldRange := by
    obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective A a
    rw [← hrs, map_div₀, ← IsScalarTower.algebraMap_apply A K S,
      ← IsScalarTower.algebraMap_apply A K S]
    exact f.fieldRange.div_mem (hcoeff r) (hcoeff s)
  have hz : z ∈ f.fieldRange := by
    refine ⟨algebraMap A[X] (FractionRing A[X]) X, ?_⟩
    rw [IsFractionRing.lift_algebraMap, hX]
  have hpoly (a : K[X]) : aeval z a ∈ f.fieldRange := by
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simpa only [map_add] using f.fieldRange.add_mem ha hb
    | monomial m c =>
      simpa only [Polynomial.aeval_monomial] using
        f.fieldRange.mul_mem (hK c) (f.fieldRange.toSubring.pow_mem hz m)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨a, b, hab⟩ := hS x
    rw [hab]
    exact f.fieldRange.div_mem (hpoly a) (hpoly b)
  let : FaithfulSMul A[X] S := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  apply IsFractionRing.of_field
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective A[X] y
  exact ⟨a, b, by rw [← hab, map_div₀, IsFractionRing.lift_algebraMap,
    IsFractionRing.lift_algebraMap]⟩

private theorem finite_integralClosure_of_normal_model
    (A B S L : Type*) [CommRing A] [IsNoetherianRing A]
    [CommRing B] [IsIntegrallyClosed B] [Algebra A B]
    [Module.Finite A B] [Field S] [Algebra B S] [Algebra A S]
    [IsScalarTower A B S] [IsFractionRing B S]
    [Field L] [Algebra A L] (f : L →ₐ[A] S) :
    Module.Finite A (integralClosure A L) := by
  let g : B →ₐ[A] integralClosure A S :=
    (IsScalarTower.toAlgHom A B S).codRestrict _ fun b =>
      (IsIntegral.of_finite A b).map (IsScalarTower.toAlgHom A B S)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (R := B) (y.property.tower_top : IsIntegral B (y : S))
    exact ⟨b, Subtype.ext hb⟩
  let : Module.Finite A (integralClosure A S) := Module.Finite.of_surjective g.toLinearMap hg
  let j := f.mapIntegralClosure
  apply Module.Finite.of_injective j.toLinearMap
  intro x y h
  exact Subtype.ext (f.injective (congrArg Subtype.val h))

private theorem finite_polynomial_integralClosure_of_pure
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : IsJapaneseRing.{u, 0} R)
    (L : Type u) [Field L] [Algebra (FractionRing R[X]) L] [Algebra R[X] L]
    [IsScalarTower R[X] (FractionRing R[X]) L]
    [FiniteDimensional (FractionRing R[X]) L]
    [IsPurelyInseparable (FractionRing R[X]) L] :
    Module.Finite R[X] (integralClosure R[X] L) := by
  let F := FractionRing R[X]
  let K := FractionRing R
  have hRL : Function.Injective (algebraMap R[X] L) := by
    rw [IsScalarTower.algebraMap_eq R[X] F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective R[X] F)
  let : Algebra R L := ((algebraMap R[X] L).comp C).toAlgebra
  let : IsScalarTower R R[X] L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr <|
    hRL.comp Polynomial.C_injective
  let : Algebra K L := FractionRing.liftAlgebra R L
  let : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  let Ω := AlgebraicClosure L
  let t : Ω := algebraMap R[X] Ω X
  have hRΩ : Function.Injective (algebraMap R[X] Ω) := by
    rw [IsScalarTower.algebraMap_eq R[X] L Ω]
    exact (algebraMap L Ω).injective.comp hRL
  have htR : Transcendental R t :=
    (transcendental_algebraMap_iff hRΩ).mpr
      (Polynomial.transcendental_X R)
  have htK : Transcendental K t := by
    intro h
    exact htR ((IsFractionRing.isAlgebraic_iff R K Ω).mpr h)
  have heval (a : R[X]) : aeval t a = algebraMap R[X] Ω a := by
    have h : (aeval t : R[X] →ₐ[R] Ω) = IsScalarTower.toAlgHom R R[X] Ω := by
      apply Polynomial.algHom_ext
      exact Polynomial.aeval_X t
    exact AlgHom.congr_fun h a
  have hF (x : F) : ∃ a b : K[X],
      algebraMap F Ω x = aeval t a / aeval t b := by
    obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective R[X] x
    refine ⟨a.map (algebraMap R K), b.map (algebraMap R K), ?_⟩
    rw [← hab, map_div₀, ← IsScalarTower.algebraMap_apply R[X] F Ω,
      ← IsScalarTower.algebraMap_apply R[X] F Ω,
      Polynomial.aeval_map_algebraMap, Polynomial.aeval_map_algebraMap, heval, heval]
  obtain ⟨p, hp⟩ := ExpChar.exists K
  let : ExpChar Ω p := expChar_of_injective_algebraMap (algebraMap K Ω).injective p
  let : ExpChar F p := (algebraMap F Ω).expChar (algebraMap F Ω).injective p
  obtain ⟨E, e, z, hEfin, _, hz, hztr, hcontain⟩ :=
    IsPurelyInseparable.exists_finite_constant_field K F L Ω p t htK hF
  let : FiniteDimensional K E := hEfin
  let : IsScalarTower R E Ω := IsScalarTower.to₁₃₄ R K E Ω
  let A := integralClosure R E
  let : Module.Finite R A := hR.finite_integralClosure_of_isFractionRing K E
  let : IsFractionRing A E := integralClosure.isFractionRing_of_finite_extension K E
  let : IsIntegrallyClosed A := integralClosure.isIntegrallyClosedOfFiniteExtension K
  let B := A[X]
  let S := IntermediateField.adjoin E {z}
  let : IsScalarTower R S Ω := IsScalarTower.to₁₃₄ R E S Ω
  let : IsScalarTower A S Ω := IsScalarTower.to₁₃₄ A E S Ω
  let : IsScalarTower R A S := IsScalarTower.to₁₂₄ R A E S
  let zS : S := ⟨z, IntermediateField.subset_adjoin E _ (by simp)⟩
  let φ : L →+* S :=
    { toFun := fun x => ⟨algebraMap L Ω x, hcontain x⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y) }
  let : Algebra R[X] S := (φ.comp (algebraMap R[X] L)).toAlgebra
  let f : L →ₐ[R[X]] S := { φ with commutes' := fun _ => rfl }
  let : IsScalarTower R R[X] S := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    apply Subtype.ext
    change algebraMap R Ω r = algebraMap L Ω (algebraMap R[X] L (C r))
    rw [← IsScalarTower.algebraMap_apply R[X] L Ω]
    exact IsScalarTower.algebraMap_apply R R[X] Ω r
  let modelMap : R[X] →ₐ[R] B := aeval (X ^ p ^ e)
  let : Algebra R[X] B := modelMap.toRingHom.toAlgebra
  let : IsScalarTower R R[X] B := IsScalarTower.of_algebraMap_eq fun r =>
    (modelMap.commutes r).symm
  have hmodelX : algebraMap R[X] B X = X ^ p ^ e := Polynomial.aeval_X (X ^ p ^ e)
  have hmodelC (r : R) : algebraMap R[X] B (C r) = C (algebraMap R A r) :=
    Polynomial.aeval_C (X ^ p ^ e) r
  let : Module.Finite R[X] B := finite_polynomial_of_power R A (p ^ e)
    (expChar_pow_pos K p e) hmodelC hmodelX
  let evalS : B →ₐ[A] S := aeval zS
  let : Algebra B S := evalS.toRingHom.toAlgebra
  let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun a =>
    (evalS.commutes a).symm
  let : IsScalarTower R B S := IsScalarTower.to₁₃₄ R A B S
  have hevalX : algebraMap B S X = zS := Polynomial.aeval_X zS
  let : IsScalarTower R[X] B S := by
    have h : (IsScalarTower.toAlgHom R B S).comp (IsScalarTower.toAlgHom R R[X] B) =
        IsScalarTower.toAlgHom R R[X] S := by
      apply Polynomial.algHom_ext
      change algebraMap B S (algebraMap R[X] B X) = algebraMap R[X] S X
      rw [hmodelX, map_pow, hevalX]
      apply Subtype.ext
      change z ^ p ^ e = algebraMap L Ω (algebraMap R[X] L X)
      rw [← IsScalarTower.algebraMap_apply R[X] L Ω]
      exact hz
    exact IsScalarTower.of_algebraMap_eq fun a => (AlgHom.congr_fun h a).symm
  have hzA : Transcendental A z :=
    hztr.restrictScalars (IsFractionRing.injective A E)
  have hzAS : Transcendental A zS :=
    (transcendental_algebraMap_iff (algebraMap S Ω).injective).mp hzA
  have hevalinj : Function.Injective (algebraMap B S) :=
    transcendental_iff_injective.mp hzAS
  have hS (x : S) : ∃ a b : E[X], x = aeval zS a / aeval zS b := by
    obtain ⟨a, b, hab⟩ := (IntermediateField.mem_adjoin_simple_iff E (x : Ω)).mp x.property
    refine ⟨a, b, ?_⟩
    apply (algebraMap S Ω).injective
    change (x : Ω) = algebraMap S Ω (aeval zS a / aeval zS b)
    rw [map_div₀]
    change (x : Ω) =
      (IsScalarTower.toAlgHom E S Ω) (aeval zS a) /
        (IsScalarTower.toAlgHom E S Ω) (aeval zS b)
    rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
    exact hab
  let : IsFractionRing B S :=
    isFractionRing_polynomial_of_rational_presentation A E S zS hevalX hevalinj hS
  exact finite_integralClosure_of_normal_model R[X] B S L f

/-- A polynomial ring over a Noetherian Japanese domain is Japanese.
The original coefficient ring need not be normal. All tested extension
fields remain in the original ambient universe, with auxiliary universe zero. -/
theorem polynomial
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : IsJapaneseRing.{u, 0} R) : IsJapaneseRing.{u, 0} R[X] := by
  intro L hL hFL hRL hT hfin
  apply integralClosure.finite_of_finite_purelyInseparable R[X] (FractionRing R[X]) L
  intro F hF hKF hRF hTF hfinite hpure
  exact finite_polynomial_integralClosure_of_pure R hR F

end IsJapaneseRing
