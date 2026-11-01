/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.HeightOneCancellation
public import Aglib.RingTheory.Kummer.RootBaseChange
public import Mathlib.RingTheory.Localization.Ideal

/-! # The original root localization at the parameter prime

Localizing the coefficient ring at the parameter prime gives the localization
of the literal root algebra at its root prime. The contraction is proved from
the original quotient map, rather than supplied as an identification.
-/

@[expose] public noncomputable section

namespace Algebra.Kummer

universe u

variable {R : Type u} [CommRing R] (N : ℕ) (f : R)

/-- The original root ideal contracts to the original parameter ideal. -/
theorem root_span_under (hN : 0 < N) :
    (Ideal.span {AdjoinRoot.root (rootPolynomial N f)} : Ideal (RootAlgebra N f)).under R =
      Ideal.span {f} := by
  ext r
  change algebraMap R (RootAlgebra N f) r ∈
    Ideal.span {AdjoinRoot.root (rootPolynomial N f)} ↔ r ∈ Ideal.span {f}
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  change algebraMap R
    (RootAlgebra N f ⧸ Ideal.span {AdjoinRoot.root (rootPolynomial N f)}) r = 0 ↔ _
  rw [← (rootQuotientEquiv N hN f).map_eq_zero_iff]
  change (rootQuotientEquiv N hN f) (algebraMap R _ r) = 0 ↔ _
  rw [AlgEquiv.commutes]
  rfl

variable [hp : (Ideal.span {f} : Ideal R).IsPrime]
  [hθ : (Ideal.span {AdjoinRoot.root (rootPolynomial N f)} :
    Ideal (RootAlgebra N f)).IsPrime]

local notation "P" => (Ideal.span {(f : R)} : Ideal R)
local notation "D" => Localization.AtPrime P
local notation "T" => RootAlgebra N f
local notation "T'" => RootAlgebra N (algebraMap R D f)
local notation "J" => (Ideal.span {AdjoinRoot.root (rootPolynomial N f)} : Ideal T)

local instance : Algebra T T' := rootBaseChangeAlgebra D N f

omit hθ in
/-- The coefficient-localized root algebra has the original root as its
maximal ideal, since its root quotient is the parameter-prime residue field. -/
theorem parameterLocalizedRoot_maximalIdeal (hN : 0 < N) :
    letI := parameterRoot_isLocalRing D (algebraMap R D f)
      (by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton f))) N hN
    IsLocalRing.maximalIdeal T' =
      Ideal.span {AdjoinRoot.root (rootPolynomial N (algebraMap R D f))} := by
  have hm : IsLocalRing.maximalIdeal D = Ideal.span {algebraMap R D f} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span]
    rw [Set.image_singleton]
  have hf : algebraMap R D f ∈ IsLocalRing.maximalIdeal D := by
    rw [hm]
    exact Ideal.subset_span (Set.mem_singleton _)
  let := parameterRoot_isLocalRing D (algebraMap R D f) hf N hN
  apply (IsLocalRing.eq_maximalIdeal _).symm
  apply Ideal.Quotient.maximal_of_isField
  apply (rootQuotientEquiv N hN (algebraMap R D f)).toRingEquiv.isField
  rw [← hm]
  exact Field.toIsField (IsLocalRing.ResidueField D)

/-- The literal coefficient localization is the localization at the original
root prime, not just at an unspecified maximal-ideal contraction. -/
theorem parameterLocalizedRoot_isLocalizationAtPrime (hN : 0 < N) :
    IsLocalization.AtPrime T' J := by
  have hf : algebraMap R D f ∈ IsLocalRing.maximalIdeal D := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton f))
  let := parameterRoot_isLocalRing D (algebraMap R D f) hf N hN
  let := rootBaseChange_isLocalization D N f (P).primeCompl
  have hdis : Disjoint (Algebra.algebraMapSubmonoid T (P).primeCompl : Set T) J := by
    apply Set.disjoint_left.mpr
    rintro x ⟨r, hr, rfl⟩ hx
    apply hr
    change r ∈ (J).under R at hx
    rwa [root_span_under N f hN] at hx
  have hmap : (J).map (algebraMap T T') = IsLocalRing.maximalIdeal T' := by
    rw [parameterLocalizedRoot_maximalIdeal N f hN, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x : T' => Ideal.span {x}) (rootBaseChangeHom_root D N f)
  have hcon : (IsLocalRing.maximalIdeal T').under T = J := by
    rw [← hmap]
    exact IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid T (P).primeCompl) T' hθ hdis
  simpa only [hcon] using
    (rootBaseChange_isLocalizationAtPrime D N f (P).primeCompl)

/-- The actual parameter localization preserves the original root algebra action. -/
def parameterLocalizedRootEquiv (hN : 0 < N) :
    Localization.AtPrime J ≃ₐ[T] T' := by
  let := parameterLocalizedRoot_isLocalizationAtPrime N f hN
  exact IsLocalization.algEquiv (J).primeCompl _ _

end Algebra.Kummer
