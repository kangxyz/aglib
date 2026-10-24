/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Nagata.RationalAdjunction
public import Aglib.RingTheory.Nagata.Polynomial
public import Aglib.RingTheory.Nagata.Finite
public import Aglib.RingTheory.Nagata.CompleteLocalSurface
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Nagata stability over surface coefficient rings

Monogenic algebras over a Nagata coefficient ring of dimension at most two
are Nagata. The actual prime quotients use polynomial Japanese stability
or the rational-adjunction normalization theorem. For injective algebraic
finite-type domain maps, a finite-generator induction also derives the
target dimension bound. The general-surface chart construction is the consumer.
Every tested field remains in Type u with auxiliary test universe zero.
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

private theorem integral_dimension_le
    (A E : Type u) [CommRing A] [CommRing E] [Algebra A E]
    [Algebra.IsIntegral A E] : ringKrullDim E ≤ ringKrullDim A := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A E))
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under (R := A) hpq

private theorem aeval_surjective_of_adjoin_eq_top
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) :
    Function.Surjective (aeval b : A[X] →ₐ[A] B) := by
  apply (AlgHom.range_eq_top _).mp
  rwa [← Algebra.adjoin_singleton_eq_range_aeval A b]

namespace IsJapaneseRing

/-- The domain part of monogenic Nagata ascent. Its prime-quotient consumer
below supplies the actual injective coefficient map. -/
theorem of_adjoin_singleton_eq_top_of_dimLE_two
    {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B))
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) :
    IsJapaneseRing.{u, 0} B := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  have hsurj := aeval_surjective_of_adjoin_eq_top b hb
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
    have hdimE : ringKrullDim E ≤ 2 := (integral_dimension_le A E).trans hdim
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
      integralClosure.finite_adjoin_singleton_of_isNagataRing_dimLE_two E L hE hdimE bL
    let : Module.Finite B (integralClosure U L) := Module.Finite.trans U _
    exact Module.Finite.equiv (integralClosure.equivOfIntegral B U L).toLinearEquiv
  · let e : A[X] ≃ₐ[A] B := AlgEquiv.ofBijective (aeval b)
      ⟨transcendental_iff_injective.mp hba, hsurj⟩
    exact hA.isJapaneseRing.polynomial.of_ringEquiv e.toRingEquiv

end IsJapaneseRing

namespace IsNagataRing

/-- Monogenic algebras over a Nagata ring of dimension at most two are
Nagata. The target need not be a domain and has no dimension premise. -/
theorem of_adjoin_singleton_eq_top_of_dimLE_two
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) :
    IsNagataRing.{u, 0} B := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  have hsurj := aeval_surjective_of_adjoin_eq_top b hb
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
  exact IsJapaneseRing.of_adjoin_singleton_eq_top_of_dimLE_two (hA.quotient p)
    ((ringKrullDim_quotient_le p).trans hdim)
    (Ideal.algebraMap_quotient_injective (R := A) (I := q)) t ht

/-- Polynomial Nagata stability for a coefficient ring of dimension at most
two. No target dimension assertion is used or inferred here. -/
theorem polynomial_of_dimLE_two
    {A : Type u} [CommRing A] (hA : IsNagataRing.{u, 0} A)
    (hdim : ringKrullDim A ≤ 2) : IsNagataRing.{u, 0} A[X] :=
  hA.of_adjoin_singleton_eq_top_of_dimLE_two hdim X (Polynomial.adjoin_X (R := A))

end IsNagataRing

private theorem nagata_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsNagataRing.{u, 0} A) (e : A ≃+* B) : IsNagataRing.{u, 0} B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : Module.Finite A B := RingHom.Finite.of_surjective e.toRingHom e.surjective
  exact hA.of_finite

private theorem dimension_le_two_of_monogenic_algebraic
    {A B : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] (hdim : ringKrullDim A ≤ 2)
    (b : B) (hb : Algebra.adjoin A ({b} : Set B) = ⊤) (hba : IsAlgebraic A b) :
    ringKrullDim B ≤ 2 := by
  obtain ⟨f, hf, hfb⟩ := hba
  have hdrop := ringKrullDim_succ_le_of_surjective (aeval b).toRingHom
    (aeval_surjective_of_adjoin_eq_top b hb)
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf) hfb
  have hdim' : ringKrullDim B + 1 ≤ ringKrullDim A + 1 := by
    simpa only [Polynomial.ringKrullDim_of_isNoetherianRing] using hdrop
  exact ENat.WithBot.add_le_add_one_right_iff.mp
    (hdim'.trans (add_le_add hdim le_rfl))

namespace IsNagataRing

/-- A finite-type injective algebraic map of domains preserves the Nagata
property in dimension at most two. The dimension bound on the target is
proved by the same actual finite-generator tower. -/
theorem of_finiteType_isAlgebraic_and_dimLE_two
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B)) :
    IsNagataRing.{u, 0} B ∧ ringKrullDim B ≤ 2 := by
  classical
  have hgen (s : Finset B) :
      IsNagataRing.{u, 0} (Algebra.adjoin A (s : Set B)) ∧
        ringKrullDim (Algebra.adjoin A (s : Set B)) ≤ 2 := by
    induction s using Finset.induction_on with
    | empty =>
      let e : Algebra.adjoin A ((∅ : Finset B) : Set B) ≃ₐ[A] A :=
        (Subalgebra.equivOfEq _ _ (show Algebra.adjoin A ((∅ : Finset B) : Set B) = ⊥ by
          simp only [Finset.coe_empty, Algebra.adjoin_empty])).trans
            (Algebra.botEquivOfInjective hinj)
      refine ⟨nagata_of_ringEquiv hA e.symm.toRingEquiv, ?_⟩
      rw [e.toRingEquiv.ringKrullDim]
      exact hdim
    | @insert x s _ ih =>
      let C := Algebra.adjoin A (s : Set B)
      let : IsNoetherianRing C := ih.1.isNoetherianRing
      let E := Algebra.adjoin C ({x} : Set B)
      let z : E := ⟨x, Algebra.self_mem_adjoin_singleton C x⟩
      have hsurj : Function.Surjective (aeval z : C[X] →ₐ[C] E) := by
        intro y
        obtain ⟨f, hf⟩ := Algebra.adjoin_eq_exists_aeval C x y
        refine ⟨f, Subtype.ext ?_⟩
        simpa only [z, Polynomial.coe_aeval_mk_apply] using hf
      have hz : Algebra.adjoin C ({z} : Set E) = ⊤ := by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact (AlgHom.range_eq_top _).mpr hsurj
      have hAC : Function.Injective (algebraMap A C) := by
        intro a b h
        apply hinj
        exact congrArg (fun c : C => (c : B)) h
      have hxC : IsAlgebraic C x :=
        (Algebra.IsAlgebraic.isAlgebraic (R := A) x).extendScalars hAC
      have hzC : IsAlgebraic C z :=
        (isAlgebraic_algHom_iff E.val Subtype.val_injective).mp hxC
      have hE : IsNagataRing.{u, 0} E :=
        ih.1.of_adjoin_singleton_eq_top_of_dimLE_two ih.2 z hz
      have hdimE : ringKrullDim E ≤ 2 :=
        dimension_le_two_of_monogenic_algebraic ih.2 z hz hzC
      have heq : E.restrictScalars A = Algebra.adjoin A ((insert x s : Finset B) : Set B) := by
        rw [Finset.coe_insert, ← Set.singleton_union, Set.union_comm]
        exact (Algebra.adjoin_union_eq_adjoin_adjoin A (s : Set B) ({x} : Set B)).symm
      let e : E ≃+* Algebra.adjoin A ((insert x s : Finset B) : Set B) :=
        (Subalgebra.equivOfEq _ _ heq).toRingEquiv
      refine ⟨nagata_of_ringEquiv hE e, ?_⟩
      rw [← e.ringKrullDim]
      exact hdimE
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A B).out
  let e : Algebra.adjoin A (s : Set B) ≃ₐ[A] B :=
    (Subalgebra.equivOfEq _ _ hs).trans Subalgebra.topEquiv
  refine ⟨nagata_of_ringEquiv (hgen s).1 e.toRingEquiv, ?_⟩
  rw [← e.toRingEquiv.ringKrullDim]
  exact (hgen s).2

/-- The Nagata conclusion of finite-type generically algebraic stability.
Generic algebraicity is represented over the original coefficient domain. -/
theorem of_finiteType_isAlgebraic_of_dimLE_two
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B)) : IsNagataRing.{u, 0} B :=
  (hA.of_finiteType_isAlgebraic_and_dimLE_two hdim hinj).1

/-- The target dimension is a consequence, not an input, of the actual
algebraic finite-generator tower used for Nagata stability. -/
theorem ringKrullDim_le_two_of_finiteType_isAlgebraic
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B)) : ringKrullDim B ≤ 2 :=
  (hA.of_finiteType_isAlgebraic_and_dimLE_two hdim hinj).2

end IsNagataRing

namespace IsNagataRing

/-- Essentially finite-type algebraic surface domains are Nagata over the actual Nagata base. -/
theorem of_essFiniteType_isAlgebraic_of_dimLE_two
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra.EssFiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : IsNagataRing.{u, 0} A) (hdim : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A B)) : IsNagataRing.{u, 0} B := by
  let S := Algebra.EssFiniteType.subalgebra A B
  let : Algebra.IsAlgebraic A S :=
    Algebra.IsAlgebraic.of_injective S.val Subtype.val_injective
  have hinjS : Function.Injective (algebraMap A S) := by
    intro a b hab
    apply hinj
    exact congrArg (fun x : S => (x : B)) hab
  have hS : IsNagataRing.{u, 0} S :=
    hA.of_finiteType_isAlgebraic_of_dimLE_two hdim hinjS
  exact IsNagataRing.of_isLocalization (Algebra.EssFiniteType.submonoid A B) hS

/-- Completeness and dimension of the original base discharge the original chart's
Nagata premise; nothing is assumed about the chart's completion. -/
theorem of_essFiniteType_isAlgebraic_of_complete_surface
    {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra.EssFiniteType A B] [Algebra.IsAlgebraic A B]
    (hA : ringKrullDim A = 2) (hinj : Function.Injective (algebraMap A B)) :
    IsNagataRing.{u, 0} B := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hA.le
  exact of_essFiniteType_isAlgebraic_of_dimLE_two
    (IsNagataRing.of_complete_local_dimLE_two A) hA.le hinj

end IsNagataRing
