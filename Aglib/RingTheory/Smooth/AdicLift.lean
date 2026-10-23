/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.AdicQuotient
public import Mathlib.RingTheory.Smooth.AdicCompletion

/-!
# Compatible lifting from a flat algebra with smooth reduction

A flat algebra with formally smooth reduction modulo an ideal lifts
specified quotient-valued maps into complete algebras. The base ideal
need only map into the target ideal. The finite-order maps retain the
original coefficient action and are compatible with the actual quotient
transitions.
-/

@[expose] public noncomputable section

namespace Algebra.FormallySmooth

variable {R C A : Type*} [CommRing R] [CommRing C] [CommRing A]
  [Algebra R C] [Algebra R A]

private theorem exists_lift_factorPow_succ [Module.Flat R C]
    (I : Ideal R) (J : Ideal A) (hIJ : I.map (algebraMap R A) ≤ J)
    (hI : (Ideal.quotientMap (I.map (algebraMap R C))
      (algebraMap R C) Ideal.le_comap_map).FormallySmooth)
    (n : ℕ) (hn : 0 < n) (g : C →ₐ[R] A ⧸ J ^ n) :
    ∃ g' : C →ₐ[R] A ⧸ J ^ (n + 1),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)).comp g' = g := by
  let Rn := R ⧸ I ^ (n + 1)
  let Cn := C ⧸ (I ^ (n + 1)).map (algebraMap R C)
  let An := A ⧸ J ^ (n + 1)
  let Ap := A ⧸ J ^ n
  have hIn : I ^ (n + 1) ≤ (J ^ (n + 1)).comap (algebraMap R A) := by
    apply Ideal.map_le_iff_le_comap.mp
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hIJ (n + 1)
  have hIp : I ^ (n + 1) ≤ (J ^ n).comap (algebraMap R A) :=
    hIn.trans (Ideal.comap_mono (Ideal.pow_le_pow_right n.le_succ))
  let : Algebra Rn An := Ideal.Quotient.algebraQuotientOfLEComap hIn
  let : Algebra Rn Ap := Ideal.Quotient.algebraQuotientOfLEComap hIp
  let : IsScalarTower R Rn An := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower R Rn Ap := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hCn : (algebraMap Rn Cn).FormallySmooth :=
    RingHom.FormallySmooth.quotientMap_pow_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance) I hI (n + 1) (by omega)
  let : FormallySmooth Rn Cn := RingHom.formallySmooth_algebraMap.mp hCn
  have hkill : (I ^ (n + 1)).map (algebraMap R C) ≤ RingHom.ker g.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change g (algebraMap R C r) = 0
    rw [g.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIp hr)
  let q : Cn →ₐ[R] Ap := Ideal.Quotient.liftₐ _ g (fun c hc ↦ hkill hc)
  let qn : Cn →ₐ[Rn] Ap := q.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let t : An →ₐ[R] Ap :=
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)
  let tn : An →ₐ[Rn] Ap := t.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have ht : Function.Surjective tn :=
    Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := J) n.le_succ)
  have htnil : IsNilpotent (RingHom.ker tn.toRingHom) := by
    change IsNilpotent (RingHom.ker
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J) n.le_succ)))
    refine ⟨2, ?_⟩
    rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
    exact Ideal.map_mk_eq_bot_of_le (Ideal.pow_le_pow_right (by omega))
  let l : Cn →ₐ[Rn] An := liftOfSurjective qn tn ht htnil
  refine ⟨(l.restrictScalars R).comp (Ideal.Quotient.mkₐ R _), ?_⟩
  ext c
  exact liftOfSurjective_apply qn tn ht htnil (Ideal.Quotient.mk _ c)

private def liftAdicQuotientAux [Module.Flat R C]
    (I : Ideal R) (J : Ideal A) (hIJ : I.map (algebraMap R A) ≤ J)
    (hI : (Ideal.quotientMap (I.map (algebraMap R C))
      (algebraMap R C) Ideal.le_comap_map).FormallySmooth)
    (f : C →ₐ[R] A ⧸ J) : (n : ℕ) → C →ₐ[R] A ⧸ J ^ n
  | 0 =>
    have : Subsingleton (A ⧸ J ^ 0) := by simp
    default
  | 1 => (Ideal.quotientEquivAlgOfEq R (show J = J ^ 1 by simp)).toAlgHom.comp f
  | n + 2 =>
    (exists_lift_factorPow_succ I J hIJ hI (n + 1) (Nat.zero_lt_succ n)
      (liftAdicQuotientAux I J hIJ hI f (n + 1))).choose

private theorem factor_comp_liftAdicQuotientAux [Module.Flat R C]
    (I : Ideal R) (J : Ideal A) (hIJ : I.map (algebraMap R A) ≤ J)
    (hI : (Ideal.quotientMap (I.map (algebraMap R C))
      (algebraMap R C) Ideal.le_comap_map).FormallySmooth)
    (f : C →ₐ[R] A ⧸ J) (n : ℕ) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right n.le_succ)).comp
      (liftAdicQuotientAux I J hIJ hI f (n + 1)) =
        liftAdicQuotientAux I J hIJ hI f n := by
  cases n with
  | zero =>
    ext
    apply eq_of_zero_eq_one
    simp [subsingleton_iff_zero_eq_one]
  | succ n =>
    exact (exists_lift_factorPow_succ I J hIJ hI (n + 1) (Nat.zero_lt_succ n)
      (liftAdicQuotientAux I J hIJ hI f (n + 1))).choose_spec

private theorem factor_comp_liftAdicQuotientAux_of_le [Module.Flat R C]
    (I : Ideal R) (J : Ideal A) (hIJ : I.map (algebraMap R A) ≤ J)
    (hI : (Ideal.quotientMap (I.map (algebraMap R C))
      (algebraMap R C) Ideal.le_comap_map).FormallySmooth)
    (f : C →ₐ[R] A ⧸ J) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
      (liftAdicQuotientAux I J hIJ hI f n) =
        liftAdicQuotientAux I J hIJ hI f m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [← Ideal.Quotient.factorₐ_comp R
      (Ideal.pow_le_pow_right n.le_succ) (Ideal.pow_le_pow_right hmn), AlgHom.comp_assoc,
      factor_comp_liftAdicQuotientAux I J hIJ hI f n, ih]

/-- A flat algebra with smooth reduction lifts a specified quotient map
into the actual adic completion, preserving the original base action. -/
theorem exists_adicCompletionEvalOneₐ_comp_eq_of_quotient [Module.Flat R C]
    (I : Ideal R) {J : Ideal A} (hIJ : I.map (algebraMap R A) ≤ J)
    (hI : (Ideal.quotientMap (I.map (algebraMap R C))
      (algebraMap R C) Ideal.le_comap_map).FormallySmooth)
    (f : C →ₐ[R] A ⧸ J) :
    ∃ g : C →ₐ[R] AdicCompletion J A,
      ((AdicCompletion.evalOneₐ J).restrictScalars R).comp g = f := by
  refine ⟨AdicCompletion.liftAlgHom J (liftAdicQuotientAux I J hIJ hI f)
    (factor_comp_liftAdicQuotientAux_of_le I J hIJ hI f), ?_⟩
  ext c
  simp [liftAdicQuotientAux]

/-- The compatible lift gives an actual map into a complete target, with
the specified quotient map and the original base action. -/
theorem exists_mkₐ_comp_eq_of_isAdicComplete_of_quotient [Module.Flat R C]
    (I : Ideal R) {J : Ideal A} [IsAdicComplete J A]
    (hIJ : I.map (algebraMap R A) ≤ J)
    (hI : (Ideal.quotientMap (I.map (algebraMap R C))
      (algebraMap R C) Ideal.le_comap_map).FormallySmooth)
    (f : C →ₐ[R] A ⧸ J) :
    ∃ g : C →ₐ[R] A, (Ideal.Quotient.mkₐ R J).comp g = f := by
  obtain ⟨g, hg⟩ := exists_adicCompletionEvalOneₐ_comp_eq_of_quotient I hIJ hI f
  refine ⟨((AdicCompletion.ofAlgEquiv J).symm.toAlgHom.restrictScalars R).comp g, ?_⟩
  ext c
  simpa using congr($hg c)

end Algebra.FormallySmooth
