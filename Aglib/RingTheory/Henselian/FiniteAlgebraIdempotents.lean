/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.Etale
public import Mathlib.RingTheory.Etale.QuasiFinite

/-!
# Idempotents in finite algebras over Henselian local rings

An actual etale neighborhood with unchanged residue field admits a section
by Henselian point lifting. The native orthogonal-idempotent splitting on
that neighborhood specializes along this section. Sums of its idempotents
lift every prescribed idempotent of the finite algebra's closed quotient.
-/

@[expose] public noncomputable section

open IsLocalRing TensorProduct
open scoped BigOperators

namespace HenselianLocalRing

universe u v

variable (R : Type u) [CommRing R] [HenselianLocalRing R]

/-- An etale neighborhood with unchanged residue field has an actual
R-valued point whose inverse image of the maximal ideal is the given prime. -/
theorem exists_etale_retraction_comap
    (T : Type u) [CommRing T] [Algebra R T] [Algebra.Etale R T]
    (P : Ideal T) [P.IsPrime] [P.LiesOver (maximalIdeal R)]
    (hP : Function.Bijective (Ideal.ResidueField.mapₐ (maximalIdeal R) P
      (Algebra.ofId R T) (P.over_def (maximalIdeal R)))) :
    ∃ ρ : T →ₐ[R] R, (maximalIdeal R).comap ρ.toRingHom = P := by
  let m := maximalIdeal R
  let ek : ResidueField R ≃ₐ[R] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (ResidueField R) m.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m)
  let eP : m.ResidueField ≃ₐ[R] P.ResidueField :=
    AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ m P (Algebra.ofId R T) (P.over_def m)) hP
  let τ : T →ₐ[R] ResidueField R :=
    ek.symm.toAlgHom.comp (eP.symm.toAlgHom.comp (IsScalarTower.toAlgHom R T P.ResidueField))
  have hτ (x : T) : τ x = 0 ↔ x ∈ P := by
    constructor
    · intro hx
      have heq := congrArg (fun y => eP (ek y)) hx
      have hz : algebraMap T P.ResidueField x = 0 := by
        simpa [τ] using heq
      exact Ideal.algebraMap_residueField_eq_zero.mp hz
    · intro hx
      simp [τ, Ideal.algebraMap_residueField_eq_zero.mpr hx]
  obtain ⟨ρ, hρ⟩ := (residue_comp_bijective_of_etale R T).2 τ
  refine ⟨ρ, ?_⟩
  ext x
  change ρ x ∈ maximalIdeal R ↔ x ∈ P
  rw [← residue_eq_zero_iff]
  have heq : residue R (ρ x) = τ x := AlgHom.congr_fun hρ x
  rw [heq]
  exact hτ x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every idempotent in the actual closed quotient of a finite algebra over
a Henselian local ring lifts to an idempotent of that same algebra. No
Noetherianity, flatness, etaleness or completeness assumption on the algebra
or the base is required. -/
theorem exists_idempotent_lift_of_finite
    (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
    (e₀ : A ⧸ (maximalIdeal R).map (algebraMap R A)) (he₀ : IsIdempotentElem e₀) :
    ∃ e : A, IsIdempotentElem e ∧
      Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)) e = e₀ := by
  classical
  let m := maximalIdeal R
  let I := m.map (algebraMap R A)
  let qA : A →+* A ⧸ I := Ideal.Quotient.mk I
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective e₀
  obtain ⟨T, hT, hAlg, hEt, P, hprime, hOver, n, e, he, Q, hQprime, hQover,
      hres, heQ, hsplit⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq (S := A) m
  let : CommRing T := hT
  let : Algebra R T := hAlg
  let : Algebra.Etale R T := hEt
  let : P.IsPrime := hprime
  let : P.LiesOver m := hOver
  let : ∀ i, (Q i).IsPrime := hQprime
  let : ∀ i, (Q i).LiesOver P := hQover
  obtain ⟨ρ, hρ⟩ := exists_etale_retraction_comap R T P hres
  let φ : T ⊗[R] A →ₐ[R] A := Algebra.TensorProduct.lift
    ((Algebra.ofId R A).comp ρ) (AlgHom.id R A) (fun _ _ => .all _ _)
  have hφ (x : A) : φ (1 ⊗ₜ[R] x) = x := by simp [φ]
  have hφT (x : T) : φ (algebraMap T (T ⊗[R] A) x) = algebraMap R A (ρ x) := by
    simp [φ, Algebra.TensorProduct.algebraMap_apply]
  let S : Finset (Fin (n + 1)) := Finset.univ.filter fun j =>
    ∃ i : Fin n, j = i.castSucc ∧ a ∉ (Q i).comap Algebra.TensorProduct.includeRight.toRingHom
  let d : Fin (n + 1) → A := fun j => φ (e j)
  have hd : CompleteOrthogonalIdempotents d := he.map φ.toRingHom
  let z : A := ∑ j ∈ S, d j
  have hz : IsIdempotentElem z := hd.toOrthogonalIdempotents.isIdempotentElem_sum
  refine ⟨z, hz, ?_⟩
  apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hz.map qA) he₀
  ext b
  let J : Ideal A := b.asIdeal.comap qA
  let : J.IsPrime := Ideal.comap_isPrime _ _
  have hJm : J.comap (algebraMap R A) = m := by
    symm
    apply (maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top')
    intro x hx
    change qA (algebraMap R A x) ∈ b.asIdeal
    have hxI : algebraMap R A x ∈ I := Ideal.mem_map_of_mem _ hx
    rw [show qA (algebraMap R A x) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hxI]
    exact b.asIdeal.zero_mem
  let L : Ideal (T ⊗[R] A) := J.comap φ.toRingHom
  let : L.IsPrime := Ideal.comap_isPrime _ _
  have hLP : L.comap (algebraMap T (T ⊗[R] A)) = P := by
    ext x
    change φ (algebraMap T (T ⊗[R] A) x) ∈ J ↔ x ∈ P
    rw [hφT]
    have hJ (r : R) : algebraMap R A r ∈ J ↔ r ∈ m :=
      Iff.of_eq (congrArg (fun K : Ideal R => r ∈ K) hJm)
    rw [hJ]
    exact Iff.of_eq (congrArg (fun K : Ideal T => x ∈ K) hρ)
  let : L.LiesOver P := ⟨hLP.symm⟩
  have hLi (i : Fin n) (hi : e i.castSucc ∉ L) :
      (Q i).comap Algebra.TensorProduct.includeRight.toRingHom = J := by
    rw [← (hsplit L inferInstance inferInstance).2 i hi]
    ext x
    change φ (1 ⊗ₜ[R] x) ∈ J ↔ x ∈ J
    rw [hφ]
  change qA z ∉ b.asIdeal ↔ e₀ ∉ b.asIdeal
  rw [← ha]
  change z ∉ J ↔ a ∉ J
  constructor
  · intro hzJ
    have hex : ∃ j ∈ S, d j ∉ J := by
      by_contra! h
      exact hzJ (J.sum_mem fun j hj => h j hj)
    obtain ⟨j, hjS, hj⟩ := hex
    obtain ⟨i, rfl, hai⟩ := (Finset.mem_filter.mp hjS).2
    have hi : e i.castSucc ∉ L := hj
    rwa [hLi i hi] at hai
  · intro haJ
    have hex : ∃ j, e j ∉ L := by
      by_contra! h
      have hone : (1 : T ⊗[R] A) ∈ L := by
        rw [← he.complete]
        exact L.sum_mem fun j _ => h j
      exact Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem L hone isUnit_one)
    obtain ⟨j, hj⟩ := hex
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · have hiS : i.castSucc ∈ S := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ⟨i, rfl, ?_⟩⟩
        rwa [hLi i hj]
      have hmul : d i.castSucc * z = d i.castSucc :=
        hd.toOrthogonalIdempotents.mul_sum_of_mem hiS
      intro hzJ
      exact hj (by
        change d i.castSucc ∈ J
        rw [← hmul]
        exact J.mul_mem_left _ hzJ)
    · exact (hj (hsplit L inferInstance inferInstance).1).elim

end HenselianLocalRing
