/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Actual étale algebras lifted across nilpotent ideals

A square Jacobian presentation supplies an actual algebra over the original
ring, with its reduction isomorphic to the prescribed quotient-base algebra.
Nilpotence lifts the unit Jacobian and also lifts finite module generators.
No Henselian, Noetherian, completeness, nontriviality or monogenic hypothesis
is imposed. These are object-existence results, not only lifts of algebra maps.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v

namespace Algebra.Etale

variable (R : Type u) [CommRing R] (I : Ideal R)

private theorem finite_of_nilpotent_quotient
    {M : Type v} [AddCommGroup M] [Module R M] (hI : IsNilpotent I)
    [Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))] : Module.Finite R M := by
  classical
  let K : Submodule R M := I • ⊤
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ K)
  choose t ht using fun i : Fin n ↦ K.mkQ_surjective (s i)
  let N : Submodule R M := Submodule.span R (Set.range t)
  have hmap : N.map K.mkQ = ⊤ := by
    change (Submodule.span R (Set.range t)).map K.mkQ = ⊤
    rw [Submodule.map_span, ← Set.range_comp]
    simpa only [Function.comp_def, ht] using hs
  have hsum : N ⊔ K = ⊤ := by
    have h := congrArg (Submodule.comap K.mkQ) hmap
    simpa only [Submodule.comap_map_eq, Submodule.ker_mkQ, Submodule.comap_top] using h
  have hp (m : ℕ) : N ⊔ I ^ m • (⊤ : Submodule R M) = ⊤ := by
    induction m with
    | zero => simp
    | succ m hm =>
      calc
        N ⊔ I ^ (m + 1) • (⊤ : Submodule R M) = N ⊔ I ^ m • K := by
          rw [pow_succ, mul_smul]
        _ = N ⊔ I ^ m • (N ⊔ K) := by
          rw [Submodule.smul_sup, ← sup_assoc,
            sup_of_le_left (Submodule.smul_le_right : I ^ m • N ≤ N)]
        _ = ⊤ := by rw [hsum]; exact hm
  obtain ⟨m, hm⟩ := hI
  have hN : N = ⊤ := by
    have hm' : I ^ m = ⊥ := hm
    simpa only [hm', Submodule.bot_smul, sup_bot_eq] using hp m
  exact Module.Finite.of_fg_top (hN ▸ Submodule.fg_span (Set.finite_range t))

-- The presentation's polynomial algebra instances are transported through the
-- original tensor presentation and its quotient equivalences in this proof.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every étale algebra over a quotient by a nilpotent ideal is the reduction
of an actual étale algebra over the original ring. The isomorphism is over
the original quotient ring, using the literal tensor base change. -/
theorem exists_nilpotent_lift (hI : IsNilpotent I)
    (B : Type v) [CommRing B] [Algebra (R ⧸ I) B] [Algebra.Etale (R ⧸ I) B] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Algebra.Etale R A ∧ Nonempty ((R ⧸ I) ⊗[R] A ≃ₐ[R ⧸ I] B) := by
  classical
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 (R ⧸ I) B :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := 0) (R := R ⧸ I) (S := B)
  let : Finite σ := hσ
  let : Finite ι := hι
  let : Fintype σ := Fintype.ofFinite σ
  choose f hf using fun j : σ ↦
    MvPolynomial.map_surjective (σ := ι) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (P.relation j)
  let A := MvPolynomial ι R ⧸ Ideal.span (Set.range f)
  let Q : Algebra.PreSubmersivePresentation R A ι σ :=
    Algebra.PreSubmersivePresentation.naive (v := f) P.map P.map_inj
  let Q₀ : Algebra.PreSubmersivePresentation (R ⧸ I) ((R ⧸ I) ⊗[R] A) ι σ :=
    Q.baseChange (R ⧸ I)
  have hrel (j : σ) : Q₀.relation j = P.relation j := hf j
  have hker : Q₀.ker = P.ker := by
    rw [← Q₀.span_range_relation_eq_ker, ← P.span_range_relation_eq_ker]
    exact congrArg Ideal.span (congrArg Set.range (funext hrel))
  let e : (R ⧸ I) ⊗[R] A ≃ₐ[R ⧸ I] B :=
    (Q₀.toPresentation.quotientEquiv.symm.restrictScalars (R ⧸ I)).trans
      ((Ideal.quotientEquivAlgOfEq (R ⧸ I) hker).trans
        (P.toPresentation.quotientEquiv.restrictScalars (R ⧸ I)))
  have he (p : MvPolynomial ι (R ⧸ I)) :
      e (MvPolynomial.aeval Q₀.val p) = MvPolynomial.aeval P.val p := by
    rw [← Q₀.algebraMap_apply, ← P.algebraMap_apply]
    change e (Q₀.toPresentation.quotientEquiv (Ideal.Quotient.mk Q₀.ker p)) = _
    simp only [e, AlgEquiv.trans_apply, AlgEquiv.coe_restrictScalars,
      AlgEquiv.symm_apply_apply, Ideal.quotientEquivAlgOfEq_mk]
    exact P.toPresentation.quotientEquiv_mk p
  have hmatrix : Q₀.jacobiMatrix = P.jacobiMatrix := by
    ext i j
    simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hrel]
    rfl
  have hjac : e Q₀.jacobian = P.jacobian := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
      hmatrix]
    simpa only [Algebra.Generators.algebraMap_apply] using he P.jacobiMatrix.det
  have hjunit : IsUnit Q₀.jacobian := by
    have h := P.jacobian_isUnit.map e.symm.toRingHom
    change IsUnit (e.symm P.jacobian) at h
    rw [← hjac, AlgEquiv.symm_apply_apply] at h
    exact h
  have hnil : IsNilpotent (I.map (algebraMap R A)) := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    change (I.map (algebraMap R A)) ^ n = ⊥
    rw [← Ideal.map_pow, show I ^ n = ⊥ from hn, Ideal.map_bot]
  have hunit : IsUnit Q.jacobian := by
    apply hnil.isUnit_quotient_mk_iff.mp
    let eQ := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I
    have ht : IsUnit (eQ (Ideal.Quotient.mk (I.map (algebraMap R A)) Q.jacobian)) := by
      rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
      simpa only [Q₀, Algebra.PreSubmersivePresentation.baseChange_jacobian] using hjunit
    have h := ht.map eQ.symm.toRingHom
    change IsUnit (eQ.symm (eQ _)) at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  let Q' : Algebra.SubmersivePresentation R A ι σ := ⟨Q, hunit⟩
  have hdim : Q'.dimension = 0 := hP
  have hA : Algebra.Etale R A :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
      (Q'.isStandardSmoothOfRelativeDimension hdim)
  exact ⟨A, inferInstance, inferInstance, hA, ⟨e⟩⟩

/-- If the prescribed quotient-base algebra is finite, the constructed lift
is finite as a module over the original base. Nilpotence alone suffices to
lift a finite generating family. -/
theorem exists_finite_nilpotent_lift (hI : IsNilpotent I)
    (B : Type v) [CommRing B] [Algebra (R ⧸ I) B]
    [Module.Finite (R ⧸ I) B] [Algebra.Etale (R ⧸ I) B] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧
        Nonempty ((R ⧸ I) ⊗[R] A ≃ₐ[R ⧸ I] B) := by
  obtain ⟨A, hA, hRA, het, ⟨e⟩⟩ := exists_nilpotent_lift R I hI B
  let : CommRing A := hA
  let : Algebra R A := hRA
  let : Module.Finite (R ⧸ I) ((R ⧸ I) ⊗[R] A) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  let : Module.Finite R ((R ⧸ I) ⊗[R] A) := Module.Finite.trans (R ⧸ I) _
  let : Module.Finite R (A ⧸ (I • (⊤ : Submodule R A))) :=
    Module.Finite.equiv (_root_.TensorProduct.quotTensorEquivQuotSMul A I)
  exact ⟨A, hA, hRA, finite_of_nilpotent_quotient R I hI, het, ⟨e⟩⟩

/-- Quotient formulation retaining the actual extended ideal and the original
quotient algebra. -/
theorem exists_finite_nilpotent_quotient_lift (hI : IsNilpotent I)
    (B : Type v) [CommRing B] [Algebra (R ⧸ I) B]
    [Module.Finite (R ⧸ I) B] [Algebra.Etale (R ⧸ I) B] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Module.Finite R A ∧ Algebra.Etale R A ∧
        Nonempty ((A ⧸ I.map (algebraMap R A)) ≃ₐ[R ⧸ I] B) := by
  obtain ⟨A, hA, hRA, hfin, het, ⟨e⟩⟩ := exists_finite_nilpotent_lift R I hI B
  let : CommRing A := hA
  let : Algebra R A := hRA
  exact ⟨A, hA, hRA, hfin, het,
    ⟨(Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).trans e⟩⟩

end Algebra.Etale
