/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.FiniteAlgebraIdempotents
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Selected local factors of finite algebras over Henselian local rings

A specified maximal ideal is isolated by an actual idempotent. Its quotient
factor is identified with the native localization at that same maximal ideal,
which is therefore finite over the original Henselian base. Henselianity of
this localization is not asserted here.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v

namespace HenselianLocalRing

/-- A specified maximal ideal of a finite algebra over a Henselian local ring
is isolated by an actual idempotent of the original algebra. -/
theorem exists_idempotent_isolating_maximal
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
    (q : Ideal A) [q.IsMaximal] :
    ∃ e : A, IsIdempotentElem e ∧ e ∉ q ∧
      ∀ P : Ideal A, P.IsMaximal → e ∉ P → P = q := by
  classical
  let m := maximalIdeal R
  have hunder (J : Ideal A) [J.IsMaximal] :
      J.comap (algebraMap R A) = m :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) J)
  obtain ⟨T, hT, hAlg, hEt, P, hprime, hOver, n, e, he, Q, hQprime, hQover,
      hres, heQ, hsplit⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq (S := A) m
  let : CommRing T := hT
  let : Algebra R T := hAlg
  let : Algebra.Etale R T := hEt
  let : P.IsPrime := hprime
  let : P.LiesOver m := hOver
  obtain ⟨ρ, hρ⟩ := exists_etale_retraction_comap R T P hres
  let φ : T ⊗[R] A →ₐ[R] A := Algebra.TensorProduct.lift
    ((Algebra.ofId R A).comp ρ) (AlgHom.id R A) (fun _ _ => .all _ _)
  have hφ (x : A) : φ (1 ⊗ₜ[R] x) = x := by simp [φ]
  have hφsurj : Function.Surjective φ := fun x => ⟨1 ⊗ₜ[R] x, hφ x⟩
  have hφT (x : T) : φ (algebraMap T (T ⊗[R] A) x) = algebraMap R A (ρ x) := by
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
  have hover (J : Ideal A) [J.IsMaximal] : (J.comap φ.toRingHom).LiesOver P := by
    constructor
    symm
    ext x
    change φ (algebraMap T (T ⊗[R] A) x) ∈ J ↔ x ∈ P
    rw [hφT]
    have hJ (r : R) : algebraMap R A r ∈ J ↔ r ∈ m :=
      Iff.of_eq (congrArg (fun K : Ideal R => r ∈ K) (hunder J))
    rw [hJ]
    exact Iff.of_eq (congrArg (fun K : Ideal T => x ∈ K) hρ)
  let L := q.comap φ.toRingHom
  let : L.IsPrime := Ideal.comap_isPrime _ _
  let : L.LiesOver P := hover q
  have hlast : e (.last n) ∈ L := (hsplit L inferInstance inferInstance).1
  have hex : ∃ i : Fin n, e i.castSucc ∉ L := by
    by_contra! h
    have hall : ∀ j : Fin (n + 1), e j ∈ L := Fin.lastCases hlast h
    exact L.one_notMem (he.complete ▸ L.sum_mem (fun j _ => hall j))
  obtain ⟨i, hi⟩ := hex
  refine ⟨φ (e i.castSucc), (he.idem i.castSucc).map φ.toRingHom, hi, ?_⟩
  intro J hJ hj
  let : J.IsMaximal := hJ
  let L' := J.comap φ.toRingHom
  let : L'.IsPrime := Ideal.comap_isPrime _ _
  let : L'.LiesOver P := hover J
  apply Ideal.comap_injective_of_surjective φ.toRingHom hφsurj
  exact ((hsplit L' inferInstance inferInstance).2 i hj).trans
    ((hsplit L inferInstance inferInstance).2 i hi).symm

end HenselianLocalRing

namespace IsLocalization

/-- The quotient attached to an isolating idempotent is the actual localization
at the specified prime, not an abstract or unselected product factor. -/
def quotientEquivAtPrimeOfIsolatingIdempotent
    {A : Type v} [CommRing A] (q : Ideal A) [q.IsPrime]
    (e : A) (he : IsIdempotentElem e) (heq : e ∉ q)
    (hisolate : ∀ P : Ideal A, P.IsMaximal → e ∉ P → P = q) :
    (A ⧸ Ideal.span {1 - e}) ≃ₐ[A] Localization.AtPrime q := by
  let D := A ⧸ Ideal.span {1 - e}
  let π : A →+* D := Ideal.Quotient.mk _
  let : IsLocalization.Away e D := IsLocalization.Away.quotient_of_isIdempotentElem he
  have hunit (a : A) (ha : a ∈ q.primeCompl) : IsUnit (algebraMap A D a) := by
    by_contra h
    obtain ⟨J, hJ, haJ⟩ := exists_max_ideal_of_mem_nonunits h
    let : J.IsMaximal := hJ
    let P := J.comap π
    have hP : P.IsMaximal := Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective
    have heP : e ∉ P := by
      intro hep
      have h1e : 1 - e ∈ P := by
        change π (1 - e) ∈ J
        rw [show π (1 - e) = 0 from
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
        exact J.zero_mem
      have hone : (1 : A) ∈ P := by
        convert P.add_mem h1e hep using 1
        ring
      exact hP.isPrime.one_notMem hone
    have hPeq := hisolate P hP heP
    change a ∈ P at haJ
    rw [hPeq] at haJ
    exact ha haJ
  let : IsLocalization q.primeCompl D :=
    IsLocalization.of_le (Submonoid.powers e) q.primeCompl
      (Submonoid.powers_le.mpr heq) hunit
  exact IsLocalization.algEquiv q.primeCompl D (Localization.AtPrime q)

end IsLocalization

namespace HenselianLocalRing

/-- A localization of a finite Henselian-base algebra at any specified maximal
ideal is finite over the base. Henselianity of the target is a separate theorem. -/
theorem finite_localizationAtPrime
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
    (q : Ideal A) [q.IsMaximal] : Module.Finite R (Localization.AtPrime q) := by
  obtain ⟨e, he, heq, hi⟩ := exists_idempotent_isolating_maximal R A q
  let E := IsLocalization.quotientEquivAtPrimeOfIsolatingIdempotent q e he heq hi
  exact Module.Finite.of_surjective (E.restrictScalars R).toLinearMap E.surjective

end HenselianLocalRing
