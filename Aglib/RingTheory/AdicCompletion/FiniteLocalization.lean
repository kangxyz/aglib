/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteAlgebra
public import Aglib.RingTheory.AdicCompletion.ChineseRemainder
public import Aglib.RingTheory.AdicCompletion.Localization
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Finiteness of completed localizations of finite algebras

The original finite algebra is completed at the extended maximal ideal. Its
Artinian residue quotient supplies the finite family of actual maximal
branches. A proved cofinal radical comparison and the existing compatible CRT
maps make each completed localization a quotient of that finite completed
algebra. The completed-base action is the canonical componentwise extension
of the original local map; no finiteness of the uncompleted localization is
assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing Function
open scoped TensorProduct BigOperators

namespace AdicCompletion

private def cofinalPowerAlgEquiv {A : Type*} [CommRing A] (I J : Ideal A)
    (hIJ : I ≤ J) (e : ℕ) (he : 0 < e) (hJI : J ^ e ≤ I) :
    AdicCompletion I A ≃ₐ[A] AdicCompletion J A := by
  let f := reindexAlgHom I J id monotone_id (fun n => Ideal.pow_right_mono hIJ n)
  let g := reindexAlgHom J I (fun n => e * n)
    (fun ⦃_ _⦄ h => Nat.mul_le_mul_left e h)
    (fun n => by simpa only [pow_mul] using Ideal.pow_right_mono hJI n)
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro x
    apply ext_evalₐ
    intro n
    change evalₐ I n (g (f x)) = _
    simp only [g, f, evalₐ_reindexAlgHom, id_eq]
    rw [Ideal.Quotient.factor_comp_apply]
    exact factor_evalₐ I (Nat.le_mul_of_pos_left n he) x
  · intro x
    apply ext_evalₐ
    intro n
    change evalₐ J n (f (g x)) = _
    simp only [g, f, evalₐ_reindexAlgHom, id_eq]
    rw [Ideal.Quotient.factor_comp_apply]
    exact factor_evalₐ J (Nat.le_mul_of_pos_left n he) x

private def residueBranchIdeal {A : Type*} [CommRing A] (I : Ideal A)
    (q : MaximalSpectrum (A ⧸ I)) : Ideal A :=
  q.asIdeal.comap (Ideal.Quotient.mk I)

private instance residueBranchIsMaximal {A : Type*} [CommRing A] (I : Ideal A)
    (q : MaximalSpectrum (A ⧸ I)) : (residueBranchIdeal I q).IsMaximal := by
  let : q.asIdeal.IsMaximal := q.isMaximal
  exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective

private theorem le_residueBranchIdeal {A : Type*} [CommRing A] (I : Ideal A)
    (q : MaximalSpectrum (A ⧸ I)) : I ≤ residueBranchIdeal I q := by
  intro a ha
  change Ideal.Quotient.mk I a ∈ q.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact q.asIdeal.zero_mem

private theorem residueBranches_pairwise {A : Type*} [CommRing A] (I : Ideal A) :
    Pairwise (IsCoprime on residueBranchIdeal I) := by
  intro q t hqt
  let q' : MaximalSpectrum A := ⟨residueBranchIdeal I q, inferInstance⟩
  let t' : MaximalSpectrum A := ⟨residueBranchIdeal I t, inferInstance⟩
  apply MaximalSpectrum.isCoprime_of_ne (I := q') (J := t')
  intro h
  apply hqt
  apply MaximalSpectrum.ext
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  exact congrArg MaximalSpectrum.asIdeal h

private theorem residueBranches_prod {A : Type*} [CommRing A] (I : Ideal A)
    [IsArtinianRing (A ⧸ I)] [Fintype (MaximalSpectrum (A ⧸ I))] :
    (∏ q : MaximalSpectrum (A ⧸ I), residueBranchIdeal I q) = I.radical := by
  have hprod := prod_pow_eq_iInf (residueBranchIdeal I) (residueBranches_pairwise I) 1
  simp only [pow_one] at hprod
  rw [hprod]
  change (⨅ q : MaximalSpectrum (A ⧸ I),
    q.asIdeal.comap (Ideal.Quotient.mk I)) = I.radical
  rw [← Ideal.comap_iInf, ← IsArtinianRing.nilradical_eq_iInf]
  change Ideal.comap (Ideal.Quotient.mk I) (⊥ : Ideal (A ⧸ I)).radical = I.radical
  rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

private def residueBranchesAlgEquiv {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsArtinianRing (A ⧸ I)] :
    AdicCompletion I A ≃ₐ[A]
      ∀ q : MaximalSpectrum (A ⧸ I), AdicCompletion (residueBranchIdeal I q) A := by
  letI : Fintype (MaximalSpectrum (A ⧸ I)) := Fintype.ofFinite _
  let J := ∏ q : MaximalSpectrum (A ⧸ I), residueBranchIdeal I q
  have hJ : J = I.radical := residueBranches_prod I
  have hIJ : I ≤ J := hJ.symm ▸ I.le_radical
  let hpow := Ideal.exists_radical_pow_le_of_fg I I.radical.fg_of_isNoetherianRing
  let n := Classical.choose hpow
  have hn : I.radical ^ n ≤ I := Classical.choose_spec hpow
  have hJI : J ^ (n + 1) ≤ I := by
    rw [hJ]
    exact (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn
  exact (cofinalPowerAlgEquiv I J hIJ (n + 1) (Nat.succ_pos n) hJI).trans
    (prodCompletionAlgEquiv (residueBranchIdeal I) (residueBranches_pairwise I))

private theorem eval_residueBranchesAlgEquiv {A : Type*} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) [IsArtinianRing (A ⧸ I)] (n : ℕ)
    (x : AdicCompletion I A) (q : MaximalSpectrum (A ⧸ I)) :
    evalₐ (residueBranchIdeal I q) n (residueBranchesAlgEquiv I x q) =
      Ideal.Quotient.factor (Ideal.pow_right_mono (le_residueBranchIdeal I q) n)
        (evalₐ I n x) := by
  let : Fintype (MaximalSpectrum (A ⧸ I)) := Fintype.ofFinite _
  change evalₐ (residueBranchIdeal I q) n
    (prodCompletionToBranch (residueBranchIdeal I) (residueBranches_pairwise I) q
      (reindexAlgHom I (∏ q : MaximalSpectrum (A ⧸ I), residueBranchIdeal I q)
        id monotone_id (fun k => Ideal.pow_right_mono
          (show I ≤ ∏ q : MaximalSpectrum (A ⧸ I), residueBranchIdeal I q from
            (residueBranches_prod I).symm ▸ I.le_radical) k) x)) = _
  rw [eval_prodCompletionToBranch, evalₐ_reindexAlgHom]
  simp only [id_eq]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  rw [← ha]
  rfl

/-- The full residue-branch comparison exists with the literal branch ideals
and its original quotient-system map at every level. -/
theorem exists_residueBranchesAlgEquiv {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsArtinianRing (A ⧸ I)] :
    ∃ e : AdicCompletion I A ≃ₐ[A]
        ∀ q : MaximalSpectrum (A ⧸ I),
          AdicCompletion (q.asIdeal.comap (Ideal.Quotient.mk I)) A,
      ∀ (n : ℕ) (x : AdicCompletion I A) (q : MaximalSpectrum (A ⧸ I)),
        evalₐ (q.asIdeal.comap (Ideal.Quotient.mk I)) n (e x q) =
          Ideal.Quotient.factor
            (Ideal.pow_right_mono (show I ≤ q.asIdeal.comap (Ideal.Quotient.mk I) from by
              intro a ha
              change Ideal.Quotient.mk I a ∈ q.asIdeal
              rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
              exact q.asIdeal.zero_mem) n)
            (evalₐ I n x) := by
  refine ⟨residueBranchesAlgEquiv I, ?_⟩
  intro n x q
  exact eval_residueBranchesAlgEquiv I n x q

/-- A maximal branch of an Artinian residue quotient is an actual quotient of the
original ideal-adic completion. Its map is the literal quotient-system map. -/
theorem reindex_to_maximal_surjective {A : Type*} [CommRing A] [IsNoetherianRing A]
    (I p : Ideal A) [p.IsMaximal] [IsArtinianRing (A ⧸ I)] (hIp : I ≤ p) :
    Function.Surjective (reindexAlgHom I p id monotone_id
      (fun n => Ideal.pow_right_mono hIp n)) := by
  classical
  let : (p.map (Ideal.Quotient.mk I)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using hIp)
  let q : MaximalSpectrum (A ⧸ I) := ⟨p.map (Ideal.Quotient.mk I), inferInstance⟩
  have hq : residueBranchIdeal I q = p := Ideal.comap_map_mk hIp
  have hsur : Function.Surjective
      (reindexAlgHom I (residueBranchIdeal I q) id monotone_id
        (fun n => Ideal.pow_right_mono (le_residueBranchIdeal I q) n)) := by
    intro y
    obtain ⟨x, hx⟩ := (residueBranchesAlgEquiv I).surjective (Pi.single q y)
    refine ⟨x, ?_⟩
    apply ext_evalₐ
    intro n
    rw [evalₐ_reindexAlgHom]
    simp only [id_eq]
    rw [← eval_residueBranchesAlgEquiv I n x q]
    rw [congrFun hx q, Pi.single_eq_same]
  have htransport : ∀ (r : Ideal A) (hIr : I ≤ r), residueBranchIdeal I q = r →
      Function.Surjective (reindexAlgHom I r id monotone_id
        (fun n => Ideal.pow_right_mono hIr n)) := by
    intro r hIr hr
    subst r
    exact hsur
  exact htransport p hIp hq

namespace FiniteLocalization

universe u

variable {B C : Type u} [CommRing B] [IsLocalRing B] [CommRing C] [Algebra B C]
  (p : Ideal C) [p.IsPrime] (hp : p.comap (algebraMap B C) = maximalIdeal B)

include hp in
/-- The original localization lies over the original closed point, so its base map is local. -/
theorem isLocalHom : IsLocalHom (algebraMap B (Localization.AtPrime p)) := by
  refine ⟨fun b hb => ?_⟩
  by_contra h
  have hmem : algebraMap B C b ∈ p := by
    change b ∈ p.comap (algebraMap B C)
    rw [hp]
    exact h
  have hloc := (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime p) p (algebraMap B C b)).mpr hmem
  exact hloc (by simpa only [← IsScalarTower.algebraMap_apply] using hb)

include hp in
/-- The original local map preserves every actual maximal-ideal power. -/
theorem maximalPower_le_comap (n : ℕ) :
    maximalIdeal B ^ n ≤ (maximalIdeal (Localization.AtPrime p) ^ n).comap
      (algebraMap B (Localization.AtPrime p)) := by
  let : IsLocalHom (algebraMap B (Localization.AtPrime p)) := isLocalHom p hp
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono
    (Ideal.map_le_iff_le_comap.mpr (IsLocalRing.maximalIdeal_comap _).ge) n

/-- The actual same-precision quotient map of the original local structural map. -/
def componentMap (n : ℕ) :
    (B ⧸ maximalIdeal B ^ n) →ₐ[B]
      Localization.AtPrime p ⧸ maximalIdeal (Localization.AtPrime p) ^ n :=
  { Ideal.quotientMap _ (algebraMap B (Localization.AtPrime p))
      (maximalPower_le_comap p hp n) with commutes' := fun _ => rfl }

/-- The canonical map on maximal-adic completions of the original local ring map. -/
def completionMap : AdicCompletion (maximalIdeal B) B →ₐ[B]
    AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) :=
  liftAlgHom (maximalIdeal (Localization.AtPrime p))
    (fun n => (componentMap p hp n).comp (evalₐ (maximalIdeal B) n))
    (fun {m n} hmn => by
      ext x
      change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
          (Ideal.quotientMap _ (algebraMap B (Localization.AtPrime p))
            (maximalPower_le_comap p hp n) (evalₐ (maximalIdeal B) n x)) =
        Ideal.quotientMap _ (algebraMap B (Localization.AtPrime p))
          (maximalPower_le_comap p hp m) (evalₐ (maximalIdeal B) m x)
      rw [← factor_evalₐ (maximalIdeal B) hmn x]
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal B) n x)
      rw [← hb]
      rfl)

/-- Every quotient component is induced by the same original local map, at the same precision. -/
@[simp]
theorem eval_completionMap (n : ℕ) (x : AdicCompletion (maximalIdeal B) B) :
    evalₐ (maximalIdeal (Localization.AtPrime p)) n (completionMap p hp x) =
      Ideal.quotientMap _ (algebraMap B (Localization.AtPrime p))
        (maximalPower_le_comap p hp n) (evalₐ (maximalIdeal B) n x) :=
  evalₐ_liftAlgHom _ _ _ _ _

/-- The completion map retains the original structural map on every original base element. -/
theorem completionMap_algebraMap (b : B) :
    completionMap p hp (algebraMap B (AdicCompletion (maximalIdeal B) B) b) =
      algebraMap (Localization.AtPrime p)
        (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))
        (algebraMap B (Localization.AtPrime p) b) :=
  (completionMap p hp).commutes b

/-- The actual canonical completed-base scalar structure, as an explicit value. -/
@[instance_reducible]
def baseAlgebra : Algebra (AdicCompletion (maximalIdeal B) B)
    (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) :=
  (completionMap p hp).toRingHom.toAlgebra

omit [p.IsPrime] in
include hp in
private theorem extended_le_prime : (maximalIdeal B).map (algebraMap B C) ≤ p :=
  Ideal.map_le_iff_le_comap.mpr hp.ge

private def tensorToLocal [p.IsMaximal] :
    AdicCompletion (maximalIdeal B) B ⊗[B] C →+*
      AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) :=
  ((localizationAlgEquiv p (Localization.AtPrime p)).toRingHom.comp
    (reindexAlgHom ((maximalIdeal B).map (algebraMap B C)) p id monotone_id
      (fun n => Ideal.pow_right_mono (extended_le_prime p hp) n)).toRingHom).comp
    (tensorToExtendedCompletionAlgHom (maximalIdeal B)).toRingHom

omit [IsLocalRing B] in
private theorem eval_tensorToExtended_left (I : Ideal B) (n : ℕ)
    (x : AdicCompletion I B) :
    evalₐ (I.map (algebraMap B C)) n
      (tensorToExtendedCompletionAlgHom I (x ⊗ₜ[B] (1 : C))) =
    Ideal.quotientMap ((I.map (algebraMap B C)) ^ n) (algebraMap B C)
      (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
      (evalₐ I n x) := by
  induction x using AdicCompletion.induction_on with | _ x =>
  change Ideal.Quotient.factor
      (show ((I.map (algebraMap B C)) ^ n • ⊤ : Ideal C) ≤
        (I.map (algebraMap B C)) ^ n by simp)
      (mapIdealQuotientEquiv (S := C) I C n
        (Submodule.Quotient.mk ((x n) • (1 : C)))) =
    Ideal.quotientMap ((I.map (algebraMap B C)) ^ n) (algebraMap B C)
      (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
      (Ideal.Quotient.mk (I ^ n) (x n))
  rw [mapIdealQuotientEquiv_mk]
  change Ideal.Quotient.mk _ ((x n) • (1 : C)) =
    Ideal.Quotient.mk _ (algebraMap B C (x n))
  rw [Algebra.smul_def, mul_one]

private theorem tensorToLocal_left [p.IsMaximal]
    (x : AdicCompletion (maximalIdeal B) B) :
    tensorToLocal p hp (x ⊗ₜ[B] (1 : C)) = completionMap p hp x := by
  apply ext_evalₐ
  intro n
  change evalₐ (maximalIdeal (Localization.AtPrime p)) n
    (localizationTo p (Localization.AtPrime p)
      (reindexAlgHom ((maximalIdeal B).map (algebraMap B C)) p id monotone_id
        (fun n => Ideal.pow_right_mono (extended_le_prime p hp) n)
        (tensorToExtendedCompletionAlgHom (maximalIdeal B) (x ⊗ₜ[B] (1 : C))))) = _
  rw [eval_localizationTo, evalₐ_reindexAlgHom, eval_tensorToExtended_left,
    eval_completionMap]
  simp only [id_eq]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal B) n x)
  rw [← hb]
  rfl

private def tensorToLocalBase [p.IsMaximal] :
    letI := baseAlgebra p hp
    AdicCompletion (maximalIdeal B) B ⊗[B] C →ₐ[AdicCompletion (maximalIdeal B) B]
      AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p) := by
  letI := baseAlgebra p hp
  refine { tensorToLocal p hp with commutes' := ?_ }
  intro x
  exact tensorToLocal_left p hp x

/-- The completion of the original localization of a finite algebra is finite over
its original completed local base, under the actual canonical completion map. -/
theorem finite [IsNoetherianRing B] [Module.Finite B C] :
    letI := baseAlgebra p hp
    Module.Finite (AdicCompletion (maximalIdeal B) B)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)) := by
  let : IsNoetherianRing C := IsNoetherianRing.of_finite B C
  let : p.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under p (by
    change (p.comap (algebraMap B C)).IsMaximal
    rw [hp]
    infer_instance)
  let I := (maximalIdeal B).map (algebraMap B C)
  let : Module.Finite B (C ⧸ I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ B I).toLinearMap Ideal.Quotient.mk_surjective
  let : Module.Finite (B ⧸ maximalIdeal B) (C ⧸ I) :=
    Module.Finite.of_restrictScalars_finite B (B ⧸ maximalIdeal B) (C ⧸ I)
  let : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field (maximalIdeal B)
  let : IsArtinianRing (C ⧸ I) := IsArtinianRing.of_finite
    (B ⧸ maximalIdeal B) (C ⧸ I)
  have hs : Function.Surjective (tensorToLocal p hp) :=
    (localizationAlgEquiv p (Localization.AtPrime p)).surjective.comp
      ((reindex_to_maximal_surjective I p (extended_le_prime p hp)).comp
        (tensorEquivExtendedCompletion (S := C) (maximalIdeal B)).surjective)
  let := baseAlgebra p hp
  exact Module.Finite.of_surjective (tensorToLocalBase p hp).toLinearMap hs

end FiniteLocalization

end AdicCompletion
