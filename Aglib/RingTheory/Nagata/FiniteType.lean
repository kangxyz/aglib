/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.RationalAdjunction.General
public import Aglib.RingTheory.Nagata.Polynomial
public import Aglib.RingTheory.Nagata.Finite
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Finite-type Nagata stability

Monogenic prime quotients first pass through the actual coefficient kernel.
The algebraic branch uses the actual finite coefficient normalization and
rational adjunction; the transcendental branch uses its actual polynomial
algebra equivalence. Finite-variable polynomial induction and the supplied
finite-type polynomial presentation then give general stability. All rings
and tested fields remain in one universe, with auxiliary universe zero.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace IsFractionRing

/-- Finite-type algebraic domain algebras induce finite extensions of the
supplied fraction fields, using their original compatible coefficient maps. -/
theorem finite_of_finiteType_isAlgebraic
    (A B K F : Type u) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field F] [Algebra B F] [IsFractionRing B F] [Algebra A F]
    [IsScalarTower A B F] [Algebra K F] [IsScalarTower A K F] :
    FiniteDimensional K F := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  let Z : Set F := algebraMap B F '' (s : Set B)
  let C : IntermediateField K F := IntermediateField.adjoin K Z
  let : Fintype Z := (s.finite_toSet.image (algebraMap B F)).fintype
  let : FiniteDimensional K C := IntermediateField.finiteDimensional_adjoin (K := K) (by
    rintro _ ⟨b, _, rfl⟩
    exact ((IsFractionRing.isAlgebraic_iff A K F).mp
      (Algebra.IsAlgebraic.isAlgebraic (R := A) b).algebraMap).isIntegral)
  have hB (b : B) : algebraMap B F b ∈ C := by
    have hle : Algebra.adjoin A (s : Set B) ≤
        (C.toSubalgebra.restrictScalars A).comap (IsScalarTower.toAlgHom A B F) := by
      apply Algebra.adjoin_le
      intro y hy
      exact IntermediateField.subset_adjoin K Z ⟨y, hy, rfl⟩
    exact hle (by rw [hs]; trivial)
  have hC : C = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective B z
    rw [← hab]
    exact C.div_mem (hB a) (hB b)
  let e : C ≃ₐ[K] F := (IntermediateField.equivOfEq hC).trans IntermediateField.topEquiv
  exact Module.Finite.equiv e.toLinearEquiv

end IsFractionRing

theorem Algebra.aeval_surjective_of_adjoin_eq_top
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) :
    Function.Surjective (aeval b : A[X] →ₐ[A] B) := by
  apply (AlgHom.range_eq_top _).mp
  rwa [← Algebra.adjoin_singleton_eq_range_aeval A b]

namespace IsJapaneseRing

/-- The domain part of monogenic Nagata ascent. Its prime-quotient consumer
below supplies the actual injective coefficient map. -/
theorem of_adjoin_singleton_eq_top
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] (hA : IsNagataRing.{u, 0} A)
    (hinj : Function.Injective (algebraMap A B))
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) :
    IsJapaneseRing.{u, 0} B := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  have hsurj := Algebra.aeval_surjective_of_adjoin_eq_top b hb
  let : Algebra.FiniteType A B := Algebra.FiniteType.of_surjective (aeval b) hsurj
  by_cases hba : IsAlgebraic A b
  · let : Algebra.IsAlgebraic A B := ⟨fun y =>
      (Algebra.isAlgebraic_adjoin_singleton_iff.mpr hba) y (by rw [hb]; trivial)⟩
    intro L hL hFL hBL hT hfin
    let K := FractionRing A
    let F := FractionRing B
    let : Module.IsTorsionFree A F := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [IsScalarTower.algebraMap_eq A B F]
      exact (IsFractionRing.injective B F).comp hinj)
    let : Algebra K F := FractionRing.liftAlgebra A F
    let : IsScalarTower A K F := FractionRing.isScalarTower_liftAlgebra A F
    let : FiniteDimensional K F := IsFractionRing.finite_of_finiteType_isAlgebraic A B K F
    let : Algebra A L := ((algebraMap B L).comp (algebraMap A B)).toAlgebra
    let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let : IsScalarTower A F L := IsScalarTower.to₁₃₄ A B F L
    let : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
    let : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let : IsScalarTower A K L := IsScalarTower.to₁₂₄ A K F L
    let : FiniteDimensional K L := Module.Finite.trans F L
    let E := integralClosure A L
    let : Module.Finite A E := hA.isJapaneseRing.finite_integralClosure_of_isFractionRing K L
    let : IsIntegrallyClosed E :=
      integralClosure.isIntegrallyClosedOfFiniteExtension (R := A) (L := L) K
    let : IsFractionRing E L := integralClosure.isFractionRing_of_finite_extension K L
    have hE : IsNagataRing.{u, 0} E := hA.of_finite
    let bL : L := algebraMap B L b
    let U := Algebra.adjoin E ({bL} : Set L)
    have hBU (y : B) : algebraMap B L y ∈ U := by
      have hle : Algebra.adjoin A ({b} : Set B) ≤
          (U.restrictScalars A).comap (IsScalarTower.toAlgHom A B L) := by
        apply Algebra.adjoin_le
        exact Set.singleton_subset_iff.mpr (Algebra.self_mem_adjoin_singleton E bL)
      exact hle (by rw [hb]; trivial)
    let β : B →ₐ[A] U := (IsScalarTower.toAlgHom A B L).codRestrict
      (U.restrictScalars A) hBU
    let : Algebra B U := β.toRingHom.toAlgebra
    let : IsScalarTower A B U := IsScalarTower.of_algHom β
    let : IsScalarTower B U L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hUint (z : U) : IsIntegral B (z : L) := by
      apply Algebra.adjoin_induction (p := fun z _ => IsIntegral B z) ?_ ?_ ?_ ?_ z.property
      · rintro z rfl
        exact isIntegral_algebraMap
      · intro e
        exact e.property.tower_top
      · intro y z _ _ hy hz
        exact hy.add hz
      · intro y z _ _ hy hz
        exact hy.mul hz
    let : Algebra.IsIntegral B U := ⟨fun z =>
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom B U L) Subtype.val_injective).mp (hUint z)⟩
    let : Algebra.FiniteType E U := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton bL)
    let : Algebra.FiniteType A U := Algebra.FiniteType.trans
      (inferInstance : Algebra.FiniteType A E) (inferInstance : Algebra.FiniteType E U)
    let : Algebra.FiniteType B U := Algebra.FiniteType.of_restrictScalars_finiteType A B U
    let : Module.Finite B U := Algebra.IsIntegral.finite
    let : Module.Finite U (integralClosure U L) :=
      integralClosure.finite_adjoin_singleton_of_isNagataRing E L hE bL
    let : Module.Finite B (integralClosure U L) := Module.Finite.trans U _
    exact Module.Finite.equiv (integralClosure.equivOfIntegral B U L).toLinearEquiv
  · let e : A[X] ≃ₐ[A] B := AlgEquiv.ofBijective (aeval b)
      ⟨transcendental_iff_injective.mp hba, hsurj⟩
    exact hA.isJapaneseRing.polynomial.of_ringEquiv e.toRingEquiv

end IsJapaneseRing

namespace IsNagataRing

/-- Monogenic algebras over a Nagata ring are
Nagata. The target need not be a domain and has no dimension premise. -/
theorem of_adjoin_singleton_eq_top
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hA : IsNagataRing.{u, 0} A)
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) :
    IsNagataRing.{u, 0} B := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  have hsurj := Algebra.aeval_surjective_of_adjoin_eq_top b hb
  let : Algebra.FiniteType A B := Algebra.FiniteType.of_surjective (aeval b) hsurj
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  refine ⟨inferInstance, ?_⟩
  intro q hq
  let p : Ideal A := q.comap (algebraMap A B)
  let D := A ⧸ p
  let T := B ⧸ q
  let : Algebra D T := inferInstance
  let : IsScalarTower A D T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let t : T := Ideal.Quotient.mk q b
  have hsurjT : Function.Surjective (aeval t : D[X] →ₐ[D] T) := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨f, hf⟩ := hsurj y
    refine ⟨f.map (algebraMap A D), ?_⟩
    rw [Polynomial.aeval_map_algebraMap D t f]
    change aeval ((Ideal.Quotient.mkₐ A q) b) f = Ideal.Quotient.mk q y
    rw [Polynomial.aeval_algHom_apply, hf]
    rfl
  have ht : Algebra.adjoin D ({t} : Set T) = ⊤ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact (AlgHom.range_eq_top _).mpr hsurjT
  exact IsJapaneseRing.of_adjoin_singleton_eq_top (hA.quotient p)
    (Ideal.algebraMap_quotient_injective (R := A) (I := q)) t ht

/-- Polynomial rings over Nagata coefficient rings are Nagata, with no dimension bound. -/
theorem polynomial
    {A : Type u} [CommRing A] (hA : IsNagataRing.{u, 0} A) :
    IsNagataRing.{u, 0} A[X] :=
  hA.of_adjoin_singleton_eq_top X (Polynomial.adjoin_X (R := A))

end IsNagataRing


theorem IsNagataRing.of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsNagataRing.{u, 0} A) (e : A ≃+* B) : IsNagataRing.{u, 0} B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module.Finite A B := RingHom.Finite.of_surjective e.toRingHom e.surjective
  exact hA.of_finite


namespace IsNagataRing

/-- Finite-variable polynomial algebras over a Nagata ring are Nagata. -/
theorem mvPolynomial_fin
    {A : Type u} [CommRing A] (hA : IsNagataRing.{u, 0} A) (n : ℕ) :
    IsNagataRing.{u, 0} (MvPolynomial (Fin n) A) := by
  induction n with
  | zero =>
    exact hA.of_ringEquiv (MvPolynomial.isEmptyRingEquiv A (Fin 0)).symm
  | succ n ih =>
    exact ih.polynomial.of_ringEquiv (MvPolynomial.finSuccEquiv A n).toRingEquiv.symm

/-- Every finite-type algebra over a Nagata ring is Nagata, without domain,
injectivity, algebraicity, separability or dimension hypotheses. -/
theorem of_finiteType
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (hA : IsNagataRing.{u, 0} A) : IsNagataRing.{u, 0} B := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  let : Algebra (MvPolynomial (Fin n) A) B := f.toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial (Fin n) A) B :=
    RingHom.Finite.of_surjective f.toRingHom hf
  exact (hA.mvPolynomial_fin n).of_finite

/-- Every essentially finite-type algebra over a Nagata ring is Nagata,
using its actual finite-type subalgebra and original localization. -/
theorem of_essFiniteType
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B]
    (hA : IsNagataRing.{u, 0} A) : IsNagataRing.{u, 0} B := by
  let S := Algebra.EssFiniteType.subalgebra A B
  have hS : IsNagataRing.{u, 0} S := hA.of_finiteType
  exact hS.of_isLocalization (Algebra.EssFiniteType.submonoid A B)

end IsNagataRing
