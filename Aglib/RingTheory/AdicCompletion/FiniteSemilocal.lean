/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteLocalization
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.Algebra.Algebra.Pi

/-!
# All actual completed local branches of a finite algebra over a local ring

The Artinian closed fibre supplies the branch set. The general proved residue
CRT comparison is composed with maximal-localization completion. Its component
maps are the original same-precision completion maps.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace AdicCompletion.FiniteSemilocal

universe u

variable (R S : Type u) [CommRing R] [IsLocalRing R]
  [CommRing S] [Algebra R S]

/-- The closed-fibre ideal obtained by extending the original base maximal ideal. -/
abbrev residueIdeal : Ideal S := (maximalIdeal R).map (algebraMap R S)

/-- The maximal points of the original algebra's closed fibre. -/
abbrev Branch := MaximalSpectrum (S ⧸ residueIdeal R S)

/-- The inverse image in the original algebra of a closed-fibre maximal ideal. -/
abbrev branchIdeal (q : Branch R S) : Ideal S :=
  q.asIdeal.comap (Ideal.Quotient.mk (residueIdeal R S))

instance branchIdeal_isMaximal (q : Branch R S) : (branchIdeal R S q).IsMaximal := by
  let : q.asIdeal.IsMaximal := q.isMaximal
  exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk (residueIdeal R S))
    Ideal.Quotient.mk_surjective

/-- The original algebra localized at the maximal ideal of the specified branch. -/
abbrev Local (q : Branch R S) := Localization.AtPrime (branchIdeal R S q)

/-- The maximal-adic completion of the specified branch's actual local ring. -/
abbrev Completed (q : Branch R S) :=
  AdicCompletion (maximalIdeal (Local R S q)) (Local R S q)

variable [Module.Finite R S]

theorem branch_contraction (q : Branch R S) :
    (branchIdeal R S q).comap (algebraMap R S) = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (show
    ((branchIdeal R S q).comap (algebraMap R S)).IsMaximal from inferInstance)

/-- Every selected original prime over the closed point occurs in the branch
set, including when its uncompleted localization is not a finite R-module. -/
def branchOfPrime (p : Ideal S) [p.IsPrime]
    (hp : p.comap (algebraMap R S) = maximalIdeal R) : Branch R S := by
  letI : p.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) p (by
    change (p.comap (algebraMap R S)).IsMaximal
    rw [hp]
    infer_instance)
  have hIp : residueIdeal R S ≤ p := Ideal.map_le_iff_le_comap.mpr hp.ge
  letI : (p.map (Ideal.Quotient.mk (residueIdeal R S))).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using hIp)
  exact ⟨p.map (Ideal.Quotient.mk (residueIdeal R S)), inferInstance⟩

theorem branchIdeal_branchOfPrime (p : Ideal S) [p.IsPrime]
    (hp : p.comap (algebraMap R S) = maximalIdeal R) :
    branchIdeal R S (branchOfPrime R S p hp) = p := by
  change (p.map (Ideal.Quotient.mk (residueIdeal R S))).comap
    (Ideal.Quotient.mk (residueIdeal R S)) = p
  exact Ideal.comap_map_mk (Ideal.map_le_iff_le_comap.mpr hp.ge)

/-- The scalar map is the previously constructed canonical local completion map. -/
@[instance_reducible]
def baseAlgebra (q : Branch R S) :
    Algebra (AdicCompletion (maximalIdeal R) R) (Completed R S q) :=
  FiniteLocalization.baseAlgebra (branchIdeal R S q) (branch_contraction R S q)

theorem baseIsScalarTower (q : Branch R S) :
    letI := baseAlgebra R S q
    IsScalarTower R (AdicCompletion (maximalIdeal R) R) (Completed R S q) := by
  let := baseAlgebra R S q
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (FiniteLocalization.completionMap_algebraMap
    (branchIdeal R S q) (branch_contraction R S q) r).symm

theorem base_algebraMap (q : Branch R S) (r : R) :
    letI := baseAlgebra R S q
    algebraMap (AdicCompletion (maximalIdeal R) R) (Completed R S q)
        (algebraMap R (AdicCompletion (maximalIdeal R) R) r) =
      algebraMap (Local R S q) (Completed R S q)
        (algebraMap R (Local R S q) r) :=
  FiniteLocalization.completionMap_algebraMap
    (branchIdeal R S q) (branch_contraction R S q) r

variable [IsNoetherianRing R] [IsNoetherianRing S]

instance local_isNoetherianRing (q : Branch R S) : IsNoetherianRing (Local R S q) :=
  IsLocalization.isNoetherianRing (branchIdeal R S q).primeCompl (Local R S q) inferInstance

omit [IsNoetherianRing S] in
/-- Finiteness belongs to the completed original localization; it is not
assumed for the uncompleted local ring. -/
theorem baseFinite (q : Branch R S) :
    letI := baseAlgebra R S q
    Module.Finite (AdicCompletion (maximalIdeal R) R) (Completed R S q) :=
  FiniteLocalization.finite (branchIdeal R S q) (branch_contraction R S q)

theorem baseIsLocalHom (q : Branch R S) :
    letI := baseAlgebra R S q
    IsLocalHom (algebraMap (AdicCompletion (maximalIdeal R) R) (Completed R S q)) := by
  let := baseAlgebra R S q
  let := baseFinite R S q
  exact ((local_hom_TFAE
    (algebraMap (AdicCompletion (maximalIdeal R) R) (Completed R S q))).out 5 1).mp
      (eq_maximalIdeal (show
        ((maximalIdeal (Completed R S q)).comap
          (algebraMap (AdicCompletion (maximalIdeal R) R) (Completed R S q))).IsMaximal
            from inferInstance))

omit [IsNoetherianRing R] [IsNoetherianRing S] in
private theorem closedFibre_artinian : IsArtinianRing (S ⧸ residueIdeal R S) := by
  let I := residueIdeal R S
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let : Algebra (R ⧸ maximalIdeal R) (S ⧸ I) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (show maximalIdeal R ≤ I.comap (algebraMap R S) from Ideal.le_comap_map)
  let : IsScalarTower R (R ⧸ maximalIdeal R) (S ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Finite R (S ⧸ I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective
  let : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ I) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ maximalIdeal R) (S ⧸ I)
  exact IsArtinianRing.of_finite (R ⧸ maximalIdeal R) _

omit [IsNoetherianRing R] [IsNoetherianRing S] in
theorem finite_branch : Finite (Branch R S) := by
  let := closedFibre_artinian R S
  infer_instance

omit [Module.Finite R S] [IsNoetherianRing R] [IsNoetherianRing S] in
private theorem eval_tensor_left (n : ℕ)
    (x : AdicCompletion (maximalIdeal R) R) :
    evalₐ (residueIdeal R S) n
      (tensorToExtendedCompletionAlgHom (maximalIdeal R) (x ⊗ₜ[R] (1 : S))) =
    Ideal.quotientMap (residueIdeal R S ^ n) (algebraMap R S)
      (by rw [residueIdeal, ← Ideal.map_pow]; exact Ideal.le_comap_map)
      (evalₐ (maximalIdeal R) n x) := by
  induction x using AdicCompletion.induction_on with | _ x =>
  change Ideal.Quotient.factor
      (show ((residueIdeal R S) ^ n • ⊤ : Ideal S) ≤ (residueIdeal R S) ^ n by simp)
      (mapIdealQuotientEquiv (S := S) (maximalIdeal R) S n
        (Submodule.Quotient.mk ((x n) • (1 : S)))) =
    Ideal.quotientMap (residueIdeal R S ^ n) (algebraMap R S)
      (by rw [residueIdeal, ← Ideal.map_pow]; exact Ideal.le_comap_map)
      (Ideal.Quotient.mk (maximalIdeal R ^ n) (x n))
  rw [mapIdealQuotientEquiv_mk]
  change Ideal.Quotient.mk _ ((x n) • (1 : S)) =
    Ideal.Quotient.mk _ (algebraMap R S (x n))
  rw [Algebra.smul_def, mul_one]

/-- The actual finite tensor product is the full product of the actual completed
local rings. The completed-base actions are the original completion maps. -/
theorem exists_tensorEquiv :
    letI := fun q => baseAlgebra R S q
    ∃ e : AdicCompletion (maximalIdeal R) R ⊗[R] S ≃ₐ[AdicCompletion (maximalIdeal R) R]
        ∀ q : Branch R S, Completed R S q,
      ∀ (s : S) (q : Branch R S), e (1 ⊗ₜ[R] s) q =
        algebraMap (Local R S q) (Completed R S q)
          (algebraMap S (Local R S q) s) := by
  let := fun q => baseAlgebra R S q
  let := closedFibre_artinian R S
  obtain ⟨e, heval⟩ := exists_residueBranchesAlgEquiv
    ((maximalIdeal R).map (algebraMap R S))
  let l : (∀ q : Branch R S, AdicCompletion (branchIdeal R S q) S) ≃ₐ[S]
      ∀ q : Branch R S, Completed R S q :=
    AlgEquiv.piCongrRight fun q => localizationAlgEquiv (branchIdeal R S q) (Local R S q)
  let t : AdicCompletion (maximalIdeal R) R ⊗[R] S ≃ₐ[R]
      ∀ q : Branch R S, Completed R S q :=
    (tensorEquivExtendedCompletion (S := S) (maximalIdeal R)).trans
      ((e.trans l).restrictScalars R)
  have hleft (x : AdicCompletion (maximalIdeal R) R) (q : Branch R S) :
      t (x ⊗ₜ[R] (1 : S)) q =
        FiniteLocalization.completionMap (branchIdeal R S q) (branch_contraction R S q) x := by
    apply ext_evalₐ
    intro n
    change evalₐ (maximalIdeal (Local R S q)) n
        (localizationTo (branchIdeal R S q) (Local R S q)
          (e (tensorToExtendedCompletionAlgHom (maximalIdeal R)
            (x ⊗ₜ[R] (1 : S))) q)) = _
    rw [eval_localizationTo, heval, eval_tensor_left,
      FiniteLocalization.eval_completionMap]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ (maximalIdeal R) n x)
    rw [← ha]
    rfl
  let eBase : AdicCompletion (maximalIdeal R) R ⊗[R] S ≃ₐ[AdicCompletion (maximalIdeal R) R]
      ∀ q : Branch R S, Completed R S q :=
    AlgEquiv.ofRingEquiv (f := t.toRingEquiv) (fun x => funext (hleft x))
  refine ⟨eBase, ?_⟩
  intro s q
  change localizationAlgEquiv (branchIdeal R S q) (Local R S q)
    (e (tensorEquivExtendedCompletion (maximalIdeal R) (1 ⊗ₜ[R] s)) q) = _
  rw [tensorEquivExtendedCompletion_one_tmul]
  rw [show e (algebraMap S (AdicCompletion (residueIdeal R S) S) s) q =
    algebraMap S (AdicCompletion (branchIdeal R S q) S) s from congrFun (e.commutes s) q]
  exact localizationAlgEquiv_algebraMap (branchIdeal R S q) (Local R S q) s

/-- The completed-base tensor algebra identified with the product of completed local branches. -/
def tensorEquiv :
    letI := fun q => baseAlgebra R S q
    AdicCompletion (maximalIdeal R) R ⊗[R] S ≃ₐ[AdicCompletion (maximalIdeal R) R]
      ∀ q : Branch R S, Completed R S q :=
  (exists_tensorEquiv R S).choose

theorem tensorEquiv_one_tmul (s : S) (q : Branch R S) :
    letI := fun q => baseAlgebra R S q
    tensorEquiv R S (1 ⊗ₜ[R] s) q =
      algebraMap (Local R S q) (Completed R S q)
        (algebraMap S (Local R S q) s) :=
  (exists_tensorEquiv R S).choose_spec s q

/-- The same comparison in the requested S tensor completed-R orientation.
Only the canonical commutation of the two tensor factors is used. -/
def tensorEquivRight :
    letI := fun q => baseAlgebra R S q
    letI : Algebra (AdicCompletion (maximalIdeal R) R)
        (S ⊗[R] AdicCompletion (maximalIdeal R) R) := Algebra.TensorProduct.rightAlgebra
    S ⊗[R] AdicCompletion (maximalIdeal R) R ≃ₐ[AdicCompletion (maximalIdeal R) R]
      ∀ q : Branch R S, Completed R S q := by
  letI := fun q => baseAlgebra R S q
  letI : Algebra (AdicCompletion (maximalIdeal R) R)
      (S ⊗[R] AdicCompletion (maximalIdeal R) R) := Algebra.TensorProduct.rightAlgebra
  let c : S ⊗[R] AdicCompletion (maximalIdeal R) R ≃ₐ[AdicCompletion (maximalIdeal R) R]
      AdicCompletion (maximalIdeal R) R ⊗[R] S :=
    AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R S (AdicCompletion (maximalIdeal R) R)).toRingEquiv)
      (fun x => by
        change Algebra.TensorProduct.comm R S (AdicCompletion (maximalIdeal R) R)
          (1 ⊗ₜ[R] x) = x ⊗ₜ[R] (1 : S)
        rw [Algebra.TensorProduct.comm_tmul])
  exact c.trans (tensorEquiv R S)

theorem tensorEquivRight_tmul_one (s : S) (q : Branch R S) :
    letI := fun q => baseAlgebra R S q
    letI : Algebra (AdicCompletion (maximalIdeal R) R)
        (S ⊗[R] AdicCompletion (maximalIdeal R) R) := Algebra.TensorProduct.rightAlgebra
    tensorEquivRight R S (s ⊗ₜ[R] 1) q =
      algebraMap (Local R S q) (Completed R S q)
        (algebraMap S (Local R S q) s) := by
  let := fun q => baseAlgebra R S q
  let : Algebra (AdicCompletion (maximalIdeal R) R)
      (S ⊗[R] AdicCompletion (maximalIdeal R) R) := Algebra.TensorProduct.rightAlgebra
  change tensorEquiv R S
    (Algebra.TensorProduct.comm R S (AdicCompletion (maximalIdeal R) R)
      (s ⊗ₜ[R] 1)) q = _
  rw [Algebra.TensorProduct.comm_tmul]
  exact tensorEquiv_one_tmul R S s q

end AdicCompletion.FiniteSemilocal
