/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalizedPrimeBranches
public import Aglib.RingTheory.AdicCompletion.DedekindBranches
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.DedekindDomain.Instances

/-! # Actual prime branches after localization of a finite Dedekind model -/

@[expose] public noncomputable section

namespace Localization

open IsDedekindDomain IsLocalRing AdicCompletion
attribute [local instance] Classical.decEq

variable {A S : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing S] [IsDedekindDomain S] [Algebra A S] [Module.IsTorsionFree A S]

/-- Original height-one primes over `p` are precisely the actual primes over `p`. -/
def heightOneOverEquivPrimesOver (p : HeightOneSpectrum A) :
    {q : HeightOneSpectrum S // q.asIdeal.under A = p.asIdeal} ≃ p.asIdeal.primesOver S where
  toFun q := ⟨q.1.asIdeal, q.1.isPrime, ⟨q.2.symm⟩⟩
  invFun q := ⟨⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot q.2⟩,
    q.2.2.over.symm⟩
  left_inv q := by apply Subtype.ext; apply HeightOneSpectrum.ext; rfl
  right_inv q := rfl

/-- Normalized ideal factors are the actual primes over a nonzero maximal ideal. -/
def primesOverEquivIdealBranch {R T : Type*} [CommRing R] [IsDomain R]
    [CommRing T] [IsDedekindDomain T] [Algebra R T] [Module.IsTorsionFree R T]
    [DecidableEq (Ideal T)] (m : Ideal R) [m.IsMaximal] (hm : m ≠ ⊥) :
    m.primesOver T ≃ IdealBranch (m.map (algebraMap R T)) where
  toFun q := ⟨q.1, Multiset.mem_toFinset.mpr
    ((Ideal.mem_primesOver_iff_mem_normalizedFactors T hm).mp q.2)⟩
  invFun q := ⟨q.1, (Ideal.mem_primesOver_iff_mem_normalizedFactors T hm).mpr
    (Multiset.mem_toFinset.mp q.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- All normalized branches of the actual finite localized model correspond to
original height-one primes over `p`, by extension and contraction of ideals. -/
def heightOneOverEquivLocalizedBranches (p : HeightOneSpectrum A) :
    let B := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
    letI := Classical.decEq (Ideal B)
    {q : HeightOneSpectrum S // q.asIdeal.under A = p.asIdeal} ≃
      IdealBranch ((maximalIdeal (Localization.AtPrime p.asIdeal)).map
        (algebraMap (Localization.AtPrime p.asIdeal) B)) := by
  classical
  let B := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  have hm : maximalIdeal (Localization.AtPrime p.asIdeal) ≠ ⊥ := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p.asIdeal]
    exact Ideal.map_ne_bot_of_ne_bot p.ne_bot
  exact (heightOneOverEquivPrimesOver p).trans
    ((IsDedekindDomain.primesOverEquivPrimesOver p.asIdeal
      (Localization.AtPrime p.asIdeal) B p.ne_bot).toEquiv.trans
        (primesOverEquivIdealBranch _ hm))

/-- The forward branch correspondence is literal ideal extension. -/
@[simp]
theorem heightOneOverEquivLocalizedBranches_apply (p : HeightOneSpectrum A)
    (q : {q : HeightOneSpectrum S // q.asIdeal.under A = p.asIdeal}) :
    (heightOneOverEquivLocalizedBranches p q).val =
      q.1.asIdeal.map (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) := rfl

/-- The inverse branch correspondence is literal ideal contraction. -/
@[simp]
theorem heightOneOverEquivLocalizedBranches_symm_apply (p : HeightOneSpectrum A)
    (Q : IdealBranch ((maximalIdeal (Localization.AtPrime p.asIdeal)).map
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))))) :
    ((heightOneOverEquivLocalizedBranches p).symm Q).1.asIdeal = Q.val.under S := rfl

/-- The original finite set of ideal factors and the actual localized factors
are matched by literal extension of primes. -/
def originalIdealBranchEquivLocalizedBranches (p : HeightOneSpectrum A) :
    IdealBranch (p.asIdeal.map (algebraMap A S)) ≃
      IdealBranch ((maximalIdeal (Localization.AtPrime p.asIdeal)).map
        (algebraMap (Localization.AtPrime p.asIdeal)
          (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))) :=
  (primesOverEquivIdealBranch p.asIdeal p.ne_bot).symm.trans
    ((heightOneOverEquivPrimesOver p).symm.trans (heightOneOverEquivLocalizedBranches p))

/-- Every original normalized branch contracts to the specified base prime. -/
theorem originalIdealBranch_under (p : HeightOneSpectrum A)
    (q : IdealBranch (p.asIdeal.map (algebraMap A S))) : q.val.under A = p.asIdeal :=
  ((primesOverEquivIdealBranch p.asIdeal p.ne_bot).symm q).2.2.over.symm

/-- The finite branch equivalence is literally ideal extension. -/
@[simp]
theorem originalIdealBranchEquivLocalizedBranches_apply (p : HeightOneSpectrum A)
    (q : IdealBranch (p.asIdeal.map (algebraMap A S))) :
    (originalIdealBranchEquivLocalizedBranches p q).val =
      q.val.map (algebraMap S
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) := rfl

/-- The actual local rings of matched finite branches are equivalent over the
localized base, not merely over the original domain. -/
def originalIdealBranchLocalEquiv (p : HeightOneSpectrum A)
    (q : IdealBranch (p.asIdeal.map (algebraMap A S))) :
    letI := basePrimeLocalAlgebra p.asIdeal q.val (originalIdealBranch_under p q)
    Localization.AtPrime (originalIdealBranchEquivLocalizedBranches p q).val ≃ₐ[
      Localization.AtPrime p.asIdeal] Localization.AtPrime q.val := by
  letI := basePrimeLocalAlgebra p.asIdeal q.val (originalIdealBranch_under p q)
  letI := basePrimeLocalTower p.asIdeal q.val (originalIdealBranch_under p q)
  let e : Localization.AtPrime (originalIdealBranchEquivLocalizedBranches p q).val ≃ₐ[S]
      Localization.AtPrime q.val :=
    atPrimeBasePrimeComplEquiv p.asIdeal q.val (originalIdealBranch_under p q)
  refine { e.toRingEquiv with commutes' := ?_ }
  intro r
  exact DFunLike.congr_fun (algEquiv_comp_localizedBase p.asIdeal e) r

end Localization
