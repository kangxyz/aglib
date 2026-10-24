/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteSemilocal
public import Aglib.RingTheory.AdicCompletion.NormalSurface
public import Aglib.RingTheory.AdicCompletion.RegularLocalRing
public import Aglib.RingTheory.Localization.FiniteRankEmbedding
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Generic degree bounds for actual completed local factors

First embed the whole finite algebra into its generic-rank free module, then
complete that injection. Every original completed local factor embeds through
the inverse of the proved full product decomposition. The fraction maps below
are universal lifts of the original completion maps.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct nonZeroDivisors

namespace AdicCompletion.FiniteSemilocal

universe u

/-- The original local base ring completed at its maximal ideal. -/
abbrev BaseCompletion (R : Type u) [CommRing R] [IsLocalRing R] :=
  AdicCompletion (maximalIdeal R) R

/-- The regular original local base supplies domainhood of its actual completion. -/
theorem baseCompletion_domain (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain (BaseCompletion R) := by
  let : IsRegularLocalRing (BaseCompletion R) :=
    (AdicCompletion.isRegularLocalRing_iff_maximalCompletion R).mp inferInstance
  exact IsRegularLocalRing.isDomain_of_regularLocal (BaseCompletion R)

variable (R S : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
  [IsNoetherianRing R] [CommRing S] [IsDomain S] [IsNoetherianRing S]
  [Algebra R S] [Module.Finite R S]

section Embedding

variable (F E : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
  [Field E] [Algebra S E] [IsFractionRing S E] [Algebra R E]
  [IsScalarTower R S E] [Algebra F E] [IsScalarTower R F E]

/-- The entire completed finite algebra has the same generic-rank free upper
bound. Each component is included through the actual full product comparison. -/
theorem exists_branch_embedding (q : Branch R S) :
    letI := baseAlgebra R S q
    ∃ j : Completed R S q →ₗ[BaseCompletion R]
        (Fin (Module.finrank F E) → BaseCompletion R), Function.Injective j := by
  classical
  let := fun q => baseAlgebra R S q
  obtain ⟨g, hg⟩ := IsFractionRing.exists_finite_rank_embedding R F S E
  let t : BaseCompletion R ⊗[R] S →ₗ[BaseCompletion R]
      BaseCompletion R ⊗[R] (Fin (Module.finrank F E) → R) :=
    TensorProduct.AlgebraTensorModule.map LinearMap.id g
  have ht : Function.Injective t :=
    AdicCompletion.tensor_map_id_left_injective_of_injective (maximalIdeal R) hg
  let a := (TensorProduct.piScalarRight R (BaseCompletion R) (BaseCompletion R)
    (Fin (Module.finrank F E))).toLinearMap.comp t
  have ha : Function.Injective a :=
    (TensorProduct.piScalarRight R (BaseCompletion R) (BaseCompletion R)
      (Fin (Module.finrank F E))).injective.comp ht
  let k : Completed R S q →ₗ[BaseCompletion R] BaseCompletion R ⊗[R] S :=
    (tensorEquiv R S).symm.toLinearMap.comp
      (LinearMap.single (BaseCompletion R) (Completed R S) q)
  have hk : Function.Injective k :=
    (tensorEquiv R S).symm.injective.comp (Pi.single_injective q)
  exact ⟨a.comp k, ha.comp hk⟩

variable [IsDomain (BaseCompletion R)]

include F E in
/-- Injectivity is proved for the canonical completed local map, using the
nonzero unit of the actual torsion-free completed factor. -/
theorem base_injective (q : Branch R S) :
    letI := baseAlgebra R S q
    Function.Injective (algebraMap (BaseCompletion R) (Completed R S q)) := by
  let := baseAlgebra R S q
  obtain ⟨j, hj⟩ := exists_branch_embedding R S F E q
  have h1 : j (1 : Completed R S q) ≠ 0 := by
    intro h
    exact one_ne_zero (hj (h.trans (_root_.map_zero j).symm))
  apply (injective_iff_map_eq_zero (algebraMap (BaseCompletion R) (Completed R S q))).mpr
  intro a ha
  have hz : a • j (1 : Completed R S q) = 0 := by
    rw [← j.map_smul]
    change j (algebraMap (BaseCompletion R) (Completed R S q) a * 1) = 0
    rw [ha, zero_mul, _root_.map_zero]
  exact (smul_eq_zero.mp hz).resolve_right h1

variable (q : Branch R S) [IsDomain (Completed R S q)]

/-- The upper fraction field receives the original injective completed-base map. -/
def fractionMap : FractionRing (BaseCompletion R) →+* FractionRing (Completed R S q) := by
  letI := baseAlgebra R S q
  exact IsFractionRing.lift (K := FractionRing (BaseCompletion R))
    (g := (algebraMap (Completed R S q) (FractionRing (Completed R S q))).comp
      (algebraMap (BaseCompletion R) (Completed R S q)))
    ((IsFractionRing.injective (Completed R S q) (FractionRing (Completed R S q))).comp
      (base_injective R S F E q))

theorem fractionMap_algebraMap (a : BaseCompletion R) :
    letI := baseAlgebra R S q
    fractionMap R S F E q (algebraMap (BaseCompletion R) (FractionRing (BaseCompletion R)) a) =
      algebraMap (Completed R S q) (FractionRing (Completed R S q))
        (algebraMap (BaseCompletion R) (Completed R S q) a) := by
  let := baseAlgebra R S q
  exact IsFractionRing.lift_algebraMap
    (K := FractionRing (BaseCompletion R))
    (g := (algebraMap (Completed R S q) (FractionRing (Completed R S q))).comp
      (algebraMap (BaseCompletion R) (Completed R S q)))
    ((IsFractionRing.injective (Completed R S q) (FractionRing (Completed R S q))).comp
      (base_injective R S F E q)) a

/-- The fraction-field algebra induced by the original completed branch map. -/
@[instance_reducible]
def fractionAlgebra : Algebra (FractionRing (BaseCompletion R))
    (FractionRing (Completed R S q)) :=
  (fractionMap R S F E q).toAlgebra

theorem fractionTower :
    letI := baseAlgebra R S q
    letI := fractionAlgebra R S F E q
    IsScalarTower (BaseCompletion R) (FractionRing (BaseCompletion R))
      (FractionRing (Completed R S q)) := by
  let := baseAlgebra R S q
  let := fractionAlgebra R S F E q
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (fractionMap_algebraMap R S F E q a).symm

/-- The actual factor field is finite over the actual completed-base fraction field. -/
theorem fraction_finite :
    letI := baseAlgebra R S q
    letI := fractionAlgebra R S F E q
    FiniteDimensional (FractionRing (BaseCompletion R)) (FractionRing (Completed R S q)) := by
  let := baseAlgebra R S q
  let := fractionAlgebra R S F E q
  let := fractionTower R S F E q
  let := baseFinite R S q
  exact IsFractionRing.finite_of_finite_algebra
    (BaseCompletion R) (Completed R S q)
    (FractionRing (BaseCompletion R)) (FractionRing (Completed R S q))

/-- Every actual completed factor has field degree bounded by the generic rank
of the whole original finite algebra. No factor count is used. -/
theorem fraction_finrank_le :
    letI := baseAlgebra R S q
    letI := fractionAlgebra R S F E q
    Module.finrank (FractionRing (BaseCompletion R)) (FractionRing (Completed R S q)) ≤
      Module.finrank F E := by
  let := baseAlgebra R S q
  let := fractionAlgebra R S F E q
  let := fractionTower R S F E q
  obtain ⟨j, hj⟩ := exists_branch_embedding R S F E q
  calc
    Module.finrank (FractionRing (BaseCompletion R)) (FractionRing (Completed R S q)) =
        Module.finrank (BaseCompletion R) (Completed R S q) :=
      IsFractionRing.finrank_eq (BaseCompletion R) (FractionRing (BaseCompletion R))
        (Completed R S q) (FractionRing (Completed R S q))
    _ ≤ Module.finrank (BaseCompletion R)
        (Fin (Module.finrank F E) → BaseCompletion R) :=
      LinearMap.finrank_le_finrank_of_injective hj
    _ = Module.finrank F E := by simp only [Module.finrank_pi, Fintype.card_fin]

theorem fraction_finrank_lt (n : ℕ) (hsmall : Module.finrank F E < n) :
    letI := baseAlgebra R S q
    letI := fractionAlgebra R S F E q
    Module.finrank (FractionRing (BaseCompletion R)) (FractionRing (Completed R S q)) < n :=
  lt_of_le_of_lt (fraction_finrank_le R S F E q) hsmall

end Embedding

section OriginalFields

variable [IsDomain (BaseCompletion R)]

/-- The original lower fraction field enters the actual completed lower field. -/
def originalBaseFractionMap (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] :
    F →+* FractionRing (BaseCompletion R) :=
  IsFractionRing.lift (K := F)
    (g := (algebraMap (BaseCompletion R) (FractionRing (BaseCompletion R))).comp
      (algebraMap R (BaseCompletion R)))
    ((IsFractionRing.injective (BaseCompletion R) (FractionRing (BaseCompletion R))).comp
      (AdicCompletion.of_injective (maximalIdeal R) R))

omit [IsDomain R] in
theorem originalBaseFractionMap_algebraMap
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F] (r : R) :
    originalBaseFractionMap R F (algebraMap R F r) =
      algebraMap (BaseCompletion R) (FractionRing (BaseCompletion R))
        (algebraMap R (BaseCompletion R) r) :=
  IsFractionRing.lift_algebraMap
    (K := F) (g := (algebraMap (BaseCompletion R) (FractionRing (BaseCompletion R))).comp
      (algebraMap R (BaseCompletion R)))
    ((IsFractionRing.injective (BaseCompletion R) (FractionRing (BaseCompletion R))).comp
      (AdicCompletion.of_injective (maximalIdeal R) R)) r

variable (q : Branch R S) [IsDomain (Completed R S q)]

omit [IsDomain R] [IsNoetherianRing R] [Module.Finite R S]
  [IsDomain (BaseCompletion R)] [IsDomain (Completed R S q)] in
/-- The original localization followed by completion is injective. No normal
or domain hypothesis is imposed on the target completion for this fact. -/
theorem original_to_factor_injective :
    Function.Injective ((algebraMap (Local R S q) (Completed R S q)).comp
      (algebraMap S (Local R S q))) :=
  (AdicCompletion.of_injective (maximalIdeal (Local R S q)) (Local R S q)).comp
    (IsLocalization.injective (Local R S q) (branchIdeal R S q).primeCompl_le_nonZeroDivisors)

/-- The original upper field enters this particular completed local factor by
the original localization and completion maps. -/
def originalFieldMap (E : Type u) [Field E] [Algebra S E] [IsFractionRing S E] :
    E →+* FractionRing (Completed R S q) :=
  IsFractionRing.lift (K := E)
    (g := (algebraMap (Completed R S q) (FractionRing (Completed R S q))).comp
      ((algebraMap (Local R S q) (Completed R S q)).comp (algebraMap S (Local R S q))))
    ((IsFractionRing.injective (Completed R S q) (FractionRing (Completed R S q))).comp
      (original_to_factor_injective R S q))

omit [IsDomain R] [IsNoetherianRing R] [Module.Finite R S]
  [IsDomain (BaseCompletion R)] in
theorem originalFieldMap_algebraMap
    (E : Type u) [Field E] [Algebra S E] [IsFractionRing S E] (s : S) :
    originalFieldMap R S q E (algebraMap S E s) =
      algebraMap (Completed R S q) (FractionRing (Completed R S q))
        (algebraMap (Local R S q) (Completed R S q) (algebraMap S (Local R S q) s)) :=
  IsFractionRing.lift_algebraMap (K := E)
    (g := (algebraMap (Completed R S q) (FractionRing (Completed R S q))).comp
      ((algebraMap (Local R S q) (Completed R S q)).comp (algebraMap S (Local R S q))))
    ((IsFractionRing.injective (Completed R S q) (FractionRing (Completed R S q))).comp
      (original_to_factor_injective R S q)) s

/-- The original and completed fraction-field inclusions form the original
commutative square, proved on the original lower ring. -/
theorem original_field_square
    (F E : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra S E] [IsFractionRing S E] [Algebra R E]
    [IsScalarTower R S E] [Algebra F E] [IsScalarTower R F E] :
    (originalFieldMap R S q E).comp (algebraMap F E) =
      (fractionMap R S F E q).comp (originalBaseFractionMap R F) := by
  let := baseAlgebra R S q
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  ext r
  change originalFieldMap R S q E (algebraMap F E (algebraMap R F r)) =
    fractionMap R S F E q (originalBaseFractionMap R F (algebraMap R F r))
  rw [← IsScalarTower.algebraMap_apply R F E,
    IsScalarTower.algebraMap_apply R S E, originalFieldMap_algebraMap,
    originalBaseFractionMap_algebraMap, fractionMap_algebraMap, base_algebraMap]
  rw [IsScalarTower.algebraMap_apply R S (Local R S q)]

end OriginalFields

omit [IsDomain R] [IsNoetherianRing R] [Module.Finite R S] in
/-- Domainhood and normality of an actual completed branch come from the
original complete surface base, local map, finite residue extension, and Nagata
surface hypotheses. Normality of S alone is deliberately insufficient here. -/
theorem completedBranch_normalDomain
    (q : Branch R S) [IsIntegrallyClosed S]
    (A0 : Type u) [CommRing A0] [IsDomain A0] [IsLocalRing A0]
    [IsAdicComplete (maximalIdeal A0) A0]
    [Algebra A0 (Local R S q)] [IsLocalHom (algebraMap A0 (Local R S q))]
    [Module.Finite (ResidueField A0) (ResidueField (Local R S q))]
    (hinj : Function.Injective (algebraMap A0 (Local R S q)))
    (hA0 : ringKrullDim A0 = 2) (hlocal : ringKrullDim (Local R S q) = 2)
    (hNag : IsNagataRing.{u, 0} (Local R S q)) :
    IsDomain (Completed R S q) ∧ IsIntegrallyClosed (Completed R S q) := by
  let : IsIntegrallyClosed (Local R S q) :=
    isIntegrallyClosed_of_isLocalization (Local R S q) (branchIdeal R S q).primeCompl
      (branchIdeal R S q).primeCompl_le_nonZeroDivisors
  exact AdicCompletion.normalDomain_of_complete_normal_surface A0 (Local R S q)
    hinj hA0 hlocal hNag

end AdicCompletion.FiniteSemilocal
