/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Congruence
public import Aglib.RingTheory.AdicCompletion.IdealMap
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Completed local rings after base change to a completion

For a finitely generated base ideal, a coefficient-algebra quotient killed by
a power of that ideal is unchanged by tensoring with the base completion.
The comparison uses the original tensor inclusion. Its compatible power
quotients are localized along the original prime complements, giving an
actual equivalence of maximal-adic completions at closed-fibre points.
No finite-generation assumption on the coefficient algebra is needed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace AdicCompletion

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The original completion projection gives coefficients in an algebra killed
by the specified power of the base ideal. -/
def nilpotentCoefficientMap (C : Type*) [CommRing C] [Algebra A C]
    (n : ℕ) (h : I ^ n ≤ RingHom.ker (algebraMap A C)) :
    AdicCompletion I A →ₐ[A] C :=
  (Ideal.Quotient.liftₐ (I ^ n) (Algebra.ofId A C) (fun _ ha ↦ h ha)).comp
    (evalₐ I n)

/-- Evaluate the completed coefficient factor in an algebra killed by a base
ideal power, retaining the original coefficient algebra as scalars. -/
def nilpotentTensorMap (C : Type*) [CommRing C] [Algebra A C]
    (n : ℕ) (h : I ^ n ≤ RingHom.ker (algebraMap A C)) :
    C ⊗[A] AdicCompletion I A →ₐ[C] C :=
  Algebra.TensorProduct.lift (AlgHom.id C C) (nilpotentCoefficientMap I C n h)
    (fun _ _ ↦ Commute.all _ _)

/-- In the tensor product with a nilpotent coefficient algebra, a completed
coefficient equals the image of its canonical finite-order evaluation. -/
theorem nilpotent_includeRight (C : Type*) [CommRing C] [Algebra A C]
    (hI : I.FG) (n : ℕ) (h : I ^ n ≤ RingHom.ker (algebraMap A C))
    (u : AdicCompletion I A) :
    Algebra.TensorProduct.includeRight (R := A) (A := C) u =
      Algebra.TensorProduct.includeLeft (R := A) (S := C)
        (nilpotentCoefficientMap I C n h u) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n u)
  have hkill :
      ((I ^ n).map (algebraMap A (AdicCompletion I A))).map
        (Algebra.TensorProduct.includeRight (R := A) (A := C)).toRingHom = ⊥ := by
    rw [Ideal.map_map, ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      ← Ideal.map_map, (Ideal.map_eq_bot_iff_le_ker _).mpr h, Ideal.map_bot]
  have hd : u - algebraMap A (AdicCompletion I A) a ∈
      (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
    apply (evalₐ_eq_iff_sub_mem I hI n _ _).mp
    rw [(evalₐ I n).commutes]
    exact ha.symm
  have he : Algebra.TensorProduct.includeRight (R := A) (A := C) u =
      Algebra.TensorProduct.includeRight (R := A) (A := C)
        (algebraMap A (AdicCompletion I A) a) := by
    apply sub_eq_zero.mp
    have hd' := Ideal.mem_map_of_mem
      (Algebra.TensorProduct.includeRight (R := A) (A := C)).toRingHom hd
    rw [hkill] at hd'
    let ι : AdicCompletion I A →ₐ[A] C ⊗[A] AdicCompletion I A :=
      Algebra.TensorProduct.includeRight
    change ι u - ι (algebraMap A (AdicCompletion I A) a) = 0
    have hd0 : ι.toRingHom (u - algebraMap A (AdicCompletion I A) a) = 0 :=
      Ideal.mem_bot.mp hd'
    have hcoe : ι.toRingHom (u - algebraMap A (AdicCompletion I A) a) =
        ι (u - algebraMap A (AdicCompletion I A) a) :=
      (congrArg
        (fun k : AdicCompletion I A →+* C ⊗[A] AdicCompletion I A ↦
          k (u - algebraMap A (AdicCompletion I A) a))
        (AlgHom.toRingHom_eq_coe ι)).trans
          (congrFun (AlgHom.coe_toRingHom ι)
            (u - algebraMap A (AdicCompletion I A) a))
    exact (map_sub ι u (algebraMap A (AdicCompletion I A) a)).symm.trans
      (hcoe.symm.trans hd0)
  have hc : nilpotentCoefficientMap I C n h u = algebraMap A C a := by
    change (Ideal.Quotient.liftₐ (I ^ n) (Algebra.ofId A C)
      (fun _ ha ↦ h ha)) (evalₐ I n u) = algebraMap A C a
    rw [← ha]
    rfl
  rw [hc]
  refine he.trans ?_
  exact congrArg (fun f : A →+* C ⊗[A] AdicCompletion I A ↦ f a)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := A) (A := C) (B := AdicCompletion I A)).symm

/-- Tensoring a nilpotent coefficient algebra with the base completion leaves
the algebra unchanged through its original tensor inclusion. -/
def nilpotentTensorEquiv (C : Type*) [CommRing C] [Algebra A C]
    (hI : I.FG) (n : ℕ) (h : I ^ n ≤ RingHom.ker (algebraMap A C)) :
    C ⊗[A] AdicCompletion I A ≃ₐ[C] C :=
  AlgEquiv.ofAlgHom (nilpotentTensorMap I C n h) Algebra.TensorProduct.includeLeft
    (Subsingleton.elim _ _)
    (by
      apply AlgHom.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul c u =>
          change Algebra.TensorProduct.includeLeft (R := A) (S := C)
            (c * nilpotentCoefficientMap I C n h u) = c ⊗ₜ[A] u
          rw [map_mul, ← nilpotent_includeRight I C hI n h u]
          simp only [Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
      | add x y hx hy =>
          simpa only [AlgHom.comp_apply, map_add, AlgHom.id_apply] using
            congrArg₂ (· + ·) hx hy)

/-- The inverse nilpotent comparison is the original tensor inclusion. -/
@[simp]
theorem nilpotentTensorEquiv_symm_apply (C : Type*) [CommRing C] [Algebra A C]
    (hI : I.FG) (n : ℕ) (h : I ^ n ≤ RingHom.ker (algebraMap A C)) (c : C) :
    (nilpotentTensorEquiv I C hI n h).symm c =
      c ⊗ₜ[A] (1 : AdicCompletion I A) := rfl

variable (B : Type*) [CommRing B] [Algebra A B]

/-- A quotient killed by a power of the base ideal is unchanged by the actual
base-completion tensor inclusion. The coefficient algebra need not be finite type. -/
def quotientTensorCompletionEquiv (hI : I.FG) (n : ℕ) (J : Ideal B)
    (h : (I ^ n).map (algebraMap A B) ≤ J) :
    B ⧸ J ≃+*
      (AdicCompletion I A ⊗[A] B) ⧸
        J.map (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A)) := by
  have hnil : I ^ n ≤ RingHom.ker (algebraMap A (B ⧸ J)) := by
    intro a ha
    change Ideal.Quotient.mk J (algebraMap A B a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h (Ideal.mem_map_of_mem _ ha))
  exact ((nilpotentTensorEquiv I (B ⧸ J) hI n hnil).symm.toRingEquiv.trans
    (Algebra.TensorProduct.comm A (B ⧸ J) (AdicCompletion I A)).toRingEquiv).trans
      (Algebra.TensorProduct.tensorQuotientEquiv
        (R := A) A B (AdicCompletion I A) J).toRingEquiv

/-- The quotient comparison is the one induced by the original coefficient
algebra's `includeRight` map. -/
@[simp]
theorem quotientTensorCompletionEquiv_mk (hI : I.FG) (n : ℕ) (J : Ideal B)
    (h : (I ^ n).map (algebraMap A B) ≤ J) (b : B) :
    quotientTensorCompletionEquiv I B hI n J h (Ideal.Quotient.mk J b) =
      Ideal.Quotient.mk
        (J.map (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A)))
        (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A) b) := by
  dsimp only [quotientTensorCompletionEquiv, RingEquiv.trans_apply]
  simp only [AlgEquiv.coe_ringEquiv]
  rw [nilpotentTensorEquiv_symm_apply, Algebra.TensorProduct.comm_tmul]
  exact Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul
    (R := A) A B (AdicCompletion I A) J 1 b

private theorem map_comap_eq_of_quotient_surjective
    {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (K : Ideal R) (Q : Ideal S) (hK : K.map f ≤ Q)
    (hsurj : Function.Surjective fun r : R ↦ Ideal.Quotient.mk (K.map f) (f r)) :
    (Q.comap f).map f = Q := by
  apply le_antisymm Ideal.map_comap_le
  intro y hy
  obtain ⟨r, hr⟩ := hsurj (Ideal.Quotient.mk (K.map f) y)
  have hd : f r - y ∈ K.map f :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hr
  have hrQ : r ∈ Q.comap f := by
    change f r ∈ Q
    simpa only [sub_add_cancel] using Q.add_mem (hK hd) hy
  have hsmall : K.map f ≤ (Q.comap f).map f :=
    Ideal.map_mono (Ideal.map_le_iff_le_comap.mp hK)
  simpa only [sub_sub_cancel] using
    ((Q.comap f).map f).sub_mem (Ideal.mem_map_of_mem f hrQ) (hsmall hd)

/-- Every ideal over the closed base ideal is the extension of its original
contraction under the actual completion tensor map. In particular, this
identifies the prime attached to a point of the closed fibre. -/
theorem tensorClosed_map_comap (hI : I.FG)
    (q : Ideal (AdicCompletion I A ⊗[A] B))
    (hclosed : I.map (algebraMap A (AdicCompletion I A ⊗[A] B)) ≤ q) :
    (q.comap (Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A))).map
        (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A)) = q := by
  let K : Ideal B := I.map (algebraMap A B)
  have hK : K.map (Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A)) ≤ q := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A) (algebraMap A B a) ∈ q
    rw [(Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A)).commutes]
    exact hclosed (Ideal.mem_map_of_mem _ ha)
  have hpow : (I ^ 1).map (algebraMap A B) ≤ K := by simp only [pow_one, K, le_refl]
  have hsurj : Function.Surjective fun b : B ↦
      Ideal.Quotient.mk (K.map (Algebra.TensorProduct.includeRight
        (R := A) (A := AdicCompletion I A)))
        (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A) b) := by
    intro z
    obtain ⟨c, hc⟩ := (quotientTensorCompletionEquiv I B hI 1 K hpow).surjective z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b, ?_⟩
    exact (quotientTensorCompletionEquiv_mk I B hI 1 K hpow b).symm.trans hc
  exact map_comap_eq_of_quotient_surjective
    (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A)) K q hK hsurj

/-- The original coefficient algebra and its completed base change have
isomorphic quotients by all powers of corresponding closed-fibre primes.
This compares the unlocalized rings; it does not identify their local rings. -/
def tensorPowerQuotientEquiv (hI : I.FG)
    (q : Ideal (AdicCompletion I A ⊗[A] B))
    (hclosed : I.map (algebraMap A (AdicCompletion I A ⊗[A] B)) ≤ q) (n : ℕ) :
    B ⧸ (q.comap (Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A))) ^ n ≃+*
        (AdicCompletion I A ⊗[A] B) ⧸ q ^ n := by
  let p : Ideal B := q.comap
    (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A))
  have hIp : I.map (algebraMap A B) ≤ p := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A) (algebraMap A B a) ∈ q
    rw [(Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A)).commutes]
    exact hclosed (Ideal.mem_map_of_mem _ ha)
  have hpow : (I ^ n).map (algebraMap A B) ≤ p ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hIp n
  have hqp : p.map (Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A)) = q :=
    tensorClosed_map_comap I B hI q hclosed
  have heq : (p ^ n).map (Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A)) = q ^ n :=
    (Ideal.map_pow (Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A)) p n).trans
        (congrArg (fun J : Ideal (AdicCompletion I A ⊗[A] B) ↦ J ^ n) hqp)
  exact (quotientTensorCompletionEquiv I B hI n (p ^ n) hpow).trans
    (Ideal.quotEquivOfEq heq)

/-- At every power, the comparison sends an original coefficient to its
image under `includeRight`, with the specified original prime on each side. -/
@[simp]
theorem tensorPowerQuotientEquiv_mk (hI : I.FG)
    (q : Ideal (AdicCompletion I A ⊗[A] B))
    (hclosed : I.map (algebraMap A (AdicCompletion I A ⊗[A] B)) ≤ q) (n : ℕ) (b : B) :
    tensorPowerQuotientEquiv I B hI q hclosed n (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk (q ^ n)
        (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A) b) := by
  dsimp only [tensorPowerQuotientEquiv, RingEquiv.trans_apply]
  rw [quotientTensorCompletionEquiv_mk, Ideal.quotEquivOfEq_mk]

/-- The actual power-quotient comparisons commute with the native reduction
maps, so that they form a comparison of the original inverse systems. -/
theorem tensorPowerQuotientEquiv_factor (hI : I.FG)
    (q : Ideal (AdicCompletion I A ⊗[A] B))
    (hclosed : I.map (algebraMap A (AdicCompletion I A ⊗[A] B)) ≤ q)
    {m n : ℕ} (hmn : m ≤ n)
    (x : B ⧸ (q.comap (Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A))) ^ n) :
    Ideal.Quotient.factorPow q hmn (tensorPowerQuotientEquiv I B hI q hclosed n x) =
      tensorPowerQuotientEquiv I B hI q hclosed m
        (Ideal.Quotient.factorPow
          (q.comap (Algebra.TensorProduct.includeRight
            (R := A) (A := AdicCompletion I A))) hmn x) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [tensorPowerQuotientEquiv_mk]
  change Ideal.Quotient.mk (q ^ m)
    (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A) b) =
      tensorPowerQuotientEquiv I B hI q hclosed m (Ideal.Quotient.mk _ b)
  rw [tensorPowerQuotientEquiv_mk]

/-- The quotient of the original prime-local ring is the localization of the
original quotient along the image of its original prime complement. -/
theorem atPrimePowerQuotient_isLocalization
    {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ) :
    IsLocalization (p.primeCompl.map (Ideal.Quotient.mk (p ^ n)))
      (Localization.AtPrime p ⧸ (p ^ n).map (algebraMap R (Localization.AtPrime p))) :=
  IsLocalization.of_surjective p.primeCompl (Localization.AtPrime p)
    (Ideal.Quotient.mk (p ^ n)) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk ((p ^ n).map (algebraMap R (Localization.AtPrime p))))
    Ideal.Quotient.mk_surjective rfl (by simp)

section LocalizationQuotients

variable {R S : Type*} [CommRing R] [CommRing S]
  (f : R →+* S) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
  (hpq : p = q.comap f)

include hpq

/-- The original quotient equivalence carries the images of the original
prime-complement monoids onto one another. -/
theorem quotientComplement_map (n : ℕ)
    (e : R ⧸ p ^ n ≃+* S ⧸ q ^ n)
    (he : ∀ r : R, e (Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk (q ^ n) (f r)) :
    (p.primeCompl.map (Ideal.Quotient.mk (p ^ n))).map e.toMonoidHom =
      q.primeCompl.map (Ideal.Quotient.mk (q ^ n)) := by
  cases n with
  | zero =>
      let : Subsingleton (S ⧸ q ^ 0) := by
        simpa only [pow_zero, Ideal.one_eq_top] using
          (inferInstance : Subsingleton (S ⧸ (⊤ : Ideal S)))
      apply Submonoid.ext
      intro z
      have hz : z = 1 := Subsingleton.elim _ _
      rw [hz]
      exact iff_of_true (Submonoid.one_mem _) (Submonoid.one_mem _)
  | succ n =>
      apply le_antisymm
      · rintro z ⟨x, hx, rfl⟩
        obtain ⟨r, hr, rfl⟩ := hx
        change r ∉ p at hr
        refine ⟨f r, ?_, ?_⟩
        · change f r ∉ q
          intro hfr
          apply hr
          rw [hpq]
          exact hfr
        · change Ideal.Quotient.mk (q ^ (n + 1)) (f r) =
            e (Ideal.Quotient.mk (p ^ (n + 1)) r)
          exact (he r).symm
      · rintro z ⟨s, hs, rfl⟩
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
          (e.symm (Ideal.Quotient.mk (q ^ (n + 1)) s))
        have her : e (Ideal.Quotient.mk (p ^ (n + 1)) r) =
            Ideal.Quotient.mk (q ^ (n + 1)) s :=
          (congrArg e hr).trans (e.apply_symm_apply _)
        have hd : f r - s ∈ q ^ (n + 1) :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ((he r).symm.trans her)
        have hdq : f r - s ∈ q :=
          (Ideal.pow_le_self (Nat.succ_ne_zero n)) hd
        have hrp : r ∉ p := by
          intro hrp
          have hfr : f r ∈ q := by
            rw [hpq] at hrp
            exact hrp
          change s ∉ q at hs
          apply hs
          simpa only [sub_sub_cancel] using q.sub_mem hfr hdq
        exact ⟨Ideal.Quotient.mk (p ^ (n + 1)) r, ⟨r, hrp, rfl⟩, her⟩

/-- Localize the actual finite-order quotient equivalence along the original
prime complements, rather than replacing either local ring by an oracle. -/
def localizedPowerQuotientEquiv (n : ℕ)
    (e : R ⧸ p ^ n ≃+* S ⧸ q ^ n)
    (he : ∀ r : R, e (Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk (q ^ n) (f r)) :
    (Localization.AtPrime p ⧸ (p ^ n).map (algebraMap R (Localization.AtPrime p))) ≃+*
      (Localization.AtPrime q ⧸ (q ^ n).map (algebraMap S (Localization.AtPrime q))) := by
  let : IsLocalization (p.primeCompl.map (Ideal.Quotient.mk (p ^ n)))
      (Localization.AtPrime p ⧸ (p ^ n).map (algebraMap R (Localization.AtPrime p))) :=
    atPrimePowerQuotient_isLocalization p n
  let : IsLocalization (q.primeCompl.map (Ideal.Quotient.mk (q ^ n)))
      (Localization.AtPrime q ⧸ (q ^ n).map (algebraMap S (Localization.AtPrime q))) :=
    atPrimePowerQuotient_isLocalization q n
  exact IsLocalization.ringEquivOfRingEquiv
    (M := p.primeCompl.map (Ideal.Quotient.mk (p ^ n)))
    (T := q.primeCompl.map (Ideal.Quotient.mk (q ^ n)))
    (Localization.AtPrime p ⧸ (p ^ n).map (algebraMap R (Localization.AtPrime p)))
    (Localization.AtPrime q ⧸ (q ^ n).map (algebraMap S (Localization.AtPrime q)))
    e (quotientComplement_map f p q hpq n e he)

/-- The localized quotient equivalence retains the original coefficient square. -/
theorem localizedPowerQuotientEquiv_mk (n : ℕ)
    (e : R ⧸ p ^ n ≃+* S ⧸ q ^ n)
    (he : ∀ r : R, e (Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk (q ^ n) (f r)) (r : R) :
    localizedPowerQuotientEquiv f p q hpq n e he
        (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime p) r)) =
      Ideal.Quotient.mk _ (algebraMap S (Localization.AtPrime q) (f r)) := by
  let : IsLocalization (p.primeCompl.map (Ideal.Quotient.mk (p ^ n)))
      (Localization.AtPrime p ⧸ (p ^ n).map (algebraMap R (Localization.AtPrime p))) :=
    atPrimePowerQuotient_isLocalization p n
  let : IsLocalization (q.primeCompl.map (Ideal.Quotient.mk (q ^ n)))
      (Localization.AtPrime q ⧸ (q ^ n).map (algebraMap S (Localization.AtPrime q))) :=
    atPrimePowerQuotient_isLocalization q n
  change IsLocalization.ringEquivOfRingEquiv
      (M := p.primeCompl.map (Ideal.Quotient.mk (p ^ n)))
      (T := q.primeCompl.map (Ideal.Quotient.mk (q ^ n)))
      (Localization.AtPrime p ⧸ (p ^ n).map (algebraMap R (Localization.AtPrime p)))
      (Localization.AtPrime q ⧸ (q ^ n).map (algebraMap S (Localization.AtPrime q)))
      e (quotientComplement_map f p q hpq n e he)
        (algebraMap (R ⧸ p ^ n) _ (Ideal.Quotient.mk (p ^ n) r)) = _
  rw [IsLocalization.ringEquivOfRingEquiv_eq, he]
  rfl

/-- Localized quotient comparison expressed using the actual maximal ideals
of the two original prime-local rings. -/
def localMaxPowerQuotientEquiv (n : ℕ)
    (e : R ⧸ p ^ n ≃+* S ⧸ q ^ n)
    (he : ∀ r : R, e (Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk (q ^ n) (f r)) :
    (Localization.AtPrime p ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) ^ n) ≃+*
      (Localization.AtPrime q ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ n) := by
  have hp : (p ^ n).map (algebraMap R (Localization.AtPrime p)) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) ^ n := by
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
  have hq : (q ^ n).map (algebraMap S (Localization.AtPrime q)) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ n := by
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal]
  exact (Ideal.quotEquivOfEq hp.symm).trans
    ((localizedPowerQuotientEquiv f p q hpq n e he).trans (Ideal.quotEquivOfEq hq))

/-- The maximal-power quotient comparison retains its original coefficient square. -/
theorem localMaxPowerQuotientEquiv_mk (n : ℕ)
    (e : R ⧸ p ^ n ≃+* S ⧸ q ^ n)
    (he : ∀ r : R, e (Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk (q ^ n) (f r)) (r : R) :
    localMaxPowerQuotientEquiv f p q hpq n e he
        (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime p) r)) =
      Ideal.Quotient.mk _ (algebraMap S (Localization.AtPrime q) (f r)) := by
  dsimp only [localMaxPowerQuotientEquiv, RingEquiv.trans_apply]
  rw [Ideal.quotEquivOfEq_mk, localizedPowerQuotientEquiv_mk, Ideal.quotEquivOfEq_mk]

/-- The quotient equivalence is induced by the original local-ring map on
every original local-ring element, not only on coefficients from R. -/
theorem localMaxPowerQuotientEquiv_localRingHom (n : ℕ)
    (e : R ⧸ p ^ n ≃+* S ⧸ q ^ n)
    (he : ∀ r : R, e (Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk (q ^ n) (f r)) (x : Localization.AtPrime p) :
    localMaxPowerQuotientEquiv f p q hpq n e he (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (Localization.localRingHom p q f hpq x) := by
  let α : Localization.AtPrime p →+*
      Localization.AtPrime q ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ n :=
    (localMaxPowerQuotientEquiv f p q hpq n e he).toRingHom.comp
      (Ideal.Quotient.mk _)
  let β : Localization.AtPrime p →+*
      Localization.AtPrime q ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ n :=
    (Ideal.Quotient.mk _).comp (Localization.localRingHom p q f hpq)
  have hαβ : α = β := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    change localMaxPowerQuotientEquiv f p q hpq n e he
        (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime p) r)) =
      Ideal.Quotient.mk _
        (Localization.localRingHom p q f hpq (algebraMap R (Localization.AtPrime p) r))
    rw [localMaxPowerQuotientEquiv_mk, Localization.localRingHom_to_map]
  exact congrArg
    (fun g : Localization.AtPrime p →+*
      Localization.AtPrime q ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime q)) ^ n ↦ g x) hαβ

/-- Quotient comparisons induced by one original local-ring map commute
with all maximal-ideal power transitions. -/
theorem localMaxPowerQuotientEquiv_factor
    (e : ∀ n : ℕ, R ⧸ p ^ n ≃+* S ⧸ q ^ n)
    (he : ∀ n (r : R), e n (Ideal.Quotient.mk (p ^ n) r) =
      Ideal.Quotient.mk (q ^ n) (f r)) {m n : ℕ} (hmn : m ≤ n)
    (x : Localization.AtPrime p ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) ^ n) :
    Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal (Localization.AtPrime q)) hmn
        (localMaxPowerQuotientEquiv f p q hpq n (e n) (he n) x) =
      localMaxPowerQuotientEquiv f p q hpq m (e m) (he m)
        (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal (Localization.AtPrime p)) hmn x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [localMaxPowerQuotientEquiv_localRingHom]
  change Ideal.Quotient.mk _ (Localization.localRingHom p q f hpq y) =
    localMaxPowerQuotientEquiv f p q hpq m (e m) (he m) (Ideal.Quotient.mk _ y)
  rw [localMaxPowerQuotientEquiv_localRingHom]

end LocalizationQuotients

section CompletionOfQuotients

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
  (e : ∀ n : ℕ, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
    Ideal.Quotient.factorPow J h (e n x) =
      e m (Ideal.Quotient.factorPow I h x))

include he

/-- The coordinate ring maps form the original compatible inverse system. -/
theorem completionOfQuotientsMap_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp
        ((e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom) =
      (e m).toRingHom.comp (AdicCompletion.evalₐ I m).toRingHom := by
  ext x
  change Ideal.Quotient.factorPow J h (e n (AdicCompletion.evalₐ I n x)) =
    e m (AdicCompletion.evalₐ I m x)
  rw [he, AdicCompletion.factor_evalₐ I h]

/-- Internal inverse-limit construction, to be instantiated only with the
actual localized quotient comparisons proved above. -/
def completionOfQuotientsMap : AdicCompletion I R →+* AdicCompletion J S :=
  AdicCompletion.liftRingHom J
    (fun n ↦ (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
    (completionOfQuotientsMap_compatible I J e he)

/-- Every coordinate of the completion comparison is the specified
original quotient equivalence. -/
theorem eval_completionOfQuotientsMap (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (completionOfQuotientsMap I J e he x) =
      e n (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J
    (fun n ↦ (e n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom)
    (completionOfQuotientsMap_compatible I J e he) n x

/-- The inverse quotient equivalences retain the original transitions. -/
theorem symm_quotient_factor {m n : ℕ} (h : m ≤ n) (x : S ⧸ J ^ n) :
    Ideal.Quotient.factorPow I h ((e n).symm x) =
      (e m).symm (Ideal.Quotient.factorPow J h x) := by
  apply (e m).injective
  rw [← he, (e n).apply_symm_apply, (e m).apply_symm_apply]

/-- The original inverse completion map is a left inverse at every coordinate. -/
theorem completionOfQuotientsMap_inverse_comp :
    (completionOfQuotientsMap J I (fun n ↦ (e n).symm)
      (symm_quotient_factor I J e he)).comp (completionOfQuotientsMap I J e he) =
        RingHom.id (AdicCompletion I R) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ I n
      (completionOfQuotientsMap J I (fun n ↦ (e n).symm)
        (symm_quotient_factor I J e he) (completionOfQuotientsMap I J e he x)) =
    AdicCompletion.evalₐ I n x
  rw [eval_completionOfQuotientsMap, eval_completionOfQuotientsMap]
  exact (e n).symm_apply_apply _

/-- The original inverse completion map is a right inverse at every coordinate. -/
theorem completionOfQuotientsMap_comp_inverse :
    (completionOfQuotientsMap I J e he).comp
      (completionOfQuotientsMap J I (fun n ↦ (e n).symm)
        (symm_quotient_factor I J e he)) = RingHom.id (AdicCompletion J S) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ J n
      (completionOfQuotientsMap I J e he
        (completionOfQuotientsMap J I (fun n ↦ (e n).symm)
          (symm_quotient_factor I J e he) x)) =
    AdicCompletion.evalₐ J n x
  rw [eval_completionOfQuotientsMap, eval_completionOfQuotientsMap]
  exact (e n).apply_symm_apply _

/-- Construct the actual completion equivalence from compatible original
power-quotient equivalences, with the proved original ring maps as inverses. -/
def completionOfQuotientsEquiv : AdicCompletion I R ≃+* AdicCompletion J S :=
  RingEquiv.ofRingHom (completionOfQuotientsMap I J e he)
    (completionOfQuotientsMap J I (fun n ↦ (e n).symm) (symm_quotient_factor I J e he))
    (completionOfQuotientsMap_comp_inverse I J e he)
    (completionOfQuotientsMap_inverse_comp I J e he)

/-- The inverse-limit equivalence is induced by the original ring map when
the proven quotient equivalences have its original coefficient square. -/
theorem completionOfQuotientsEquiv_algebraMap
    (f : R →+* S)
    (hf : ∀ n (r : R), e n (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk (J ^ n) (f r)) (r : R) :
    completionOfQuotientsEquiv I J e he (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion J S) (f r) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ J n
      (completionOfQuotientsMap I J e he (AdicCompletion.of I R r)) =
    AdicCompletion.evalₐ J n (AdicCompletion.of J S (f r))
  rw [eval_completionOfQuotientsMap, AdicCompletion.evalₐ_of, hf,
    AdicCompletion.evalₐ_of]

end CompletionOfQuotients

/-- The original completion map of the actual prime-local ring, retaining
one native ring and completion-algebra presentation at every use. -/
def atPrimeCompletionMap {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Localization.AtPrime p →+*
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p) :=
  algebraMap (Localization.AtPrime p) _

/-- The shared prime-local completion map is the native algebra map. -/
theorem atPrimeCompletionMap_eq {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    atPrimeCompletionMap p = algebraMap (Localization.AtPrime p) _ := rfl

section LocalCompletions

variable {R S : Type*} [CommRing R] [CommRing S]
  (f : R →+* S) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
  (hpq : p = q.comap f)
  (e : ∀ n : ℕ, R ⧸ p ^ n ≃+* S ⧸ q ^ n)
  (he : ∀ n (r : R), e n (Ideal.Quotient.mk (p ^ n) r) =
    Ideal.Quotient.mk (q ^ n) (f r))

include hpq he

/-- Compatible power-quotient equivalences induced by the original
coefficient map identify the completions of its actual prime-local rings. -/
def localCompletionsEquiv :
    AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :=
  completionOfQuotientsEquiv _ _
    (fun n ↦ localMaxPowerQuotientEquiv f p q hpq n (e n) (he n))
    (localMaxPowerQuotientEquiv_factor f p q hpq e he)

/-- The completed local-ring comparison is induced by the original
local-ring homomorphism on every original local element. -/
theorem localCompletionsEquiv_algebraMap (x : Localization.AtPrime p) :
    localCompletionsEquiv f p q hpq e he
        (atPrimeCompletionMap p x) =
      atPrimeCompletionMap q (Localization.localRingHom p q f hpq x) :=
  completionOfQuotientsEquiv_algebraMap _ _ _ _ (Localization.localRingHom p q f hpq)
    (fun n ↦ localMaxPowerQuotientEquiv_localRingHom f p q hpq n (e n) (he n)) x

end LocalCompletions

/-- The original tensor coefficient map, with one shared ring-homomorphism
presentation for all prime, localization and completion comparisons. -/
def tensorComparisonRingHom : B →+* AdicCompletion I A ⊗[A] B :=
  (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A)).toRingHom

/-- The shared ring map is the underlying original `includeRight` map. -/
theorem tensorComparisonRingHom_eq : tensorComparisonRingHom I B =
    (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A)).toRingHom := rfl

/-- The shared ring map retains every original tensor coefficient. -/
theorem tensorComparisonRingHom_apply (b : B) : tensorComparisonRingHom I B b =
    Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A) b := by
  change (Algebra.TensorProduct.includeRight
    (R := A) (A := AdicCompletion I A)).toRingHom b = _
  exact (congrArg
    (fun g : B →+* AdicCompletion I A ⊗[A] B ↦ g b)
    (AlgHom.toRingHom_eq_coe (Algebra.TensorProduct.includeRight
      (R := A) (A := AdicCompletion I A)))).trans
        (congrFun (AlgHom.coe_toRingHom (Algebra.TensorProduct.includeRight
          (R := A) (A := AdicCompletion I A))) b)

section TensorLocalCompletions

variable {A : Type*} [CommRing A] (I : Ideal A) (B : Type*) [CommRing B] [Algebra A B]
  (hI : I.FG) (q : Ideal (AdicCompletion I A ⊗[A] B)) [q.IsPrime]
  (hclosed : I.map (algebraMap A (AdicCompletion I A ⊗[A] B)) ≤ q)

omit [q.IsPrime] in
/-- Passing from the original tensor algebra map to its underlying ring
map leaves the contracted prime unchanged. -/
theorem tensorComap_toRingHom : q.comap (tensorComparisonRingHom I B) =
    q.comap (Algebra.TensorProduct.includeRight (R := A) (A := AdicCompletion I A)) :=
  (congrArg (fun g : B →+* AdicCompletion I A ⊗[A] B ↦ q.comap g)
    (tensorComparisonRingHom_eq I B)).trans
      ((congrArg (fun g : B →+* AdicCompletion I A ⊗[A] B ↦ q.comap g)
        (AlgHom.toRingHom_eq_coe (Algebra.TensorProduct.includeRight
          (R := A) (A := AdicCompletion I A)))).trans
            (Ideal.comap_coe (Algebra.TensorProduct.includeRight
              (R := A) (A := AdicCompletion I A)) q))

include hI hclosed

/-- The proved power-quotient comparison with the literal prime contracted
through the underlying original ring homomorphism. -/
def tensorRingPowerQuotientEquiv (n : ℕ) :
    B ⧸ (q.comap (tensorComparisonRingHom I B)) ^ n ≃+*
      (AdicCompletion I A ⊗[A] B) ⧸ q ^ n :=
  (Ideal.quotEquivOfEq
    (congrArg (fun J : Ideal B ↦ J ^ n) (tensorComap_toRingHom I B q))).trans
      (tensorPowerQuotientEquiv I B hI q hclosed n)

omit [q.IsPrime] in
/-- The ring-map presentation retains the same original tensor coefficient square. -/
theorem tensorRingPowerQuotientEquiv_mk (n : ℕ) (b : B) :
    tensorRingPowerQuotientEquiv I B hI q hclosed n (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk (q ^ n) (tensorComparisonRingHom I B b) := by
  dsimp only [tensorRingPowerQuotientEquiv, RingEquiv.trans_apply]
  rw [Ideal.quotEquivOfEq_mk, tensorPowerQuotientEquiv_mk]
  apply congrArg (Ideal.Quotient.mk (q ^ n))
  exact (tensorComparisonRingHom_apply I B b).symm

/-- The desired actual affine completed-local-ring comparison, constructed
through original prime complements and finite-order quotient maps.
The inferred return type retains the exact native ring presentation used by
`localCompletionsEquiv` for both prime localizations and their completions. -/
def tensorLocalCompletionsEquiv :=
  localCompletionsEquiv (tensorComparisonRingHom I B)
    (q.comap (tensorComparisonRingHom I B)) q rfl
    (tensorRingPowerQuotientEquiv I B hI q hclosed)
    (tensorRingPowerQuotientEquiv_mk I B hI q hclosed)

/-- The actual completion comparison is induced by the original tensor
local-ring map, rather than by an unrelated ring equivalence. -/
theorem tensorLocalCompletionsEquiv_algebraMap
    (x : Localization.AtPrime (q.comap (tensorComparisonRingHom I B))) :
    tensorLocalCompletionsEquiv I B hI q hclosed
        (atPrimeCompletionMap (q.comap (tensorComparisonRingHom I B)) x) =
      atPrimeCompletionMap q
        (Localization.localRingHom (q.comap (tensorComparisonRingHom I B)) q
          (tensorComparisonRingHom I B) rfl x) :=
  localCompletionsEquiv_algebraMap (tensorComparisonRingHom I B)
    (q.comap (tensorComparisonRingHom I B)) q rfl
    (tensorRingPowerQuotientEquiv I B hI q hclosed)
    (tensorRingPowerQuotientEquiv_mk I B hI q hclosed) x

end TensorLocalCompletions

end AdicCompletion
