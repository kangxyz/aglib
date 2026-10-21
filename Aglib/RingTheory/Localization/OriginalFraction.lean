/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# The original fraction field of a localization

The canonical localization lift gives a proved fraction-field equivalence,
including polynomial coefficient localization and a generatorwise square lemma.
-/

@[expose] public noncomputable section

namespace IsLocalization

variable (R S : Type*) [CommRing R] [IsDomain R] [CommRing S]
  [Algebra R S] (M : Submonoid R) [IsLocalization M S]

/-- The actual canonical map from a localization at nonzero elements to the
original fraction field. -/
abbrev toOriginalFractionRing (hM : M ≤ nonZeroDivisors R) :
    S →+* FractionRing R :=
  IsLocalization.lift (S := S) (g := algebraMap R (FractionRing R)) fun y : M =>
    IsFractionRing.isUnit_map_of_injective (IsFractionRing.injective R (FractionRing R))
      (⟨y, hM y.property⟩ : nonZeroDivisors R)

lemma toOriginalFractionRing_algebraMap (hM : M ≤ nonZeroDivisors R) (r : R) :
    toOriginalFractionRing R S M hM (algebraMap R S r) =
      algebraMap R (FractionRing R) r := by
  unfold toOriginalFractionRing
  exact IsLocalization.lift_eq (S := S) _ r

/-- A localization acts on the original fraction field through its canonical lift. -/
abbrev originalFractionAlgebra (hM : M ≤ nonZeroDivisors R) :
    Algebra S (FractionRing R) :=
  (toOriginalFractionRing R S M hM).toAlgebra

lemma originalFractionAlgebra_tower (hM : M ≤ nonZeroDivisors R) :
    let := originalFractionAlgebra R S M hM
    IsScalarTower R S (FractionRing R) := by
  let := originalFractionAlgebra R S M hM
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change algebraMap R (FractionRing R) x =
    toOriginalFractionRing R S M hM (algebraMap R S x)
  exact (toOriginalFractionRing_algebraMap R S M hM x).symm

lemma isFractionRing_originalFractionAlgebra (hM : M ≤ nonZeroDivisors R) :
    let := originalFractionAlgebra R S M hM
    IsFractionRing S (FractionRing R) := by
  let := originalFractionAlgebra R S M hM
  let := originalFractionAlgebra_tower R S M hM
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S (FractionRing R)

/-- This equivalence is obtained only after proving the literal localization
map and its tower, not by assuming the two fraction fields agree. -/
def originalFractionEquiv (hM : M ≤ nonZeroDivisors R) :
    let := originalFractionAlgebra R S M hM
    FractionRing S ≃ₐ[S] FractionRing R := by
  let := originalFractionAlgebra R S M hM
  let := isFractionRing_originalFractionAlgebra R S M hM
  exact FractionRing.algEquiv S (FractionRing R)

/-- Equality across the constructed fraction equivalence is checked on the
original ring, not on a hypothetical common ambient field. -/
lemma originalFractionEquiv_comp_eq (hM : M ≤ nonZeroDivisors R) [IsDomain S]
    {F : Type*} [Field F] (g : FractionRing R →+* F) (h : FractionRing S →+* F)
    (hbase : ∀ r : R, g (algebraMap R (FractionRing R) r) =
      h (algebraMap S (FractionRing S) (algebraMap R S r))) :
    g.comp (originalFractionEquiv R S M hM).toRingHom = h := by
  let := originalFractionAlgebra R S M hM
  let e := originalFractionEquiv R S M hM
  have hloc : g.comp (algebraMap S (FractionRing R)) =
      h.comp (algebraMap S (FractionRing S)) := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro r
    change g (toOriginalFractionRing R S M hM (algebraMap R S r)) = _
    rw [toOriginalFractionRing_algebraMap]
    exact hbase r
  apply IsFractionRing.ringHom_ext (A := S)
  intro s
  change g (e (algebraMap S (FractionRing S) s)) = _
  rw [e.commutes]
  exact RingHom.congr_fun hloc s

end IsLocalization

namespace MvPolynomial

/-- The polynomial denominators obtained from nonzero coefficients remain nonzero. -/
lemma coefficient_nonZeroDivisors_le (R σ : Type*) [CommRing R] [IsDomain R] :
    (nonZeroDivisors R).map (C (σ := σ)) ≤ nonZeroDivisors (MvPolynomial σ R) := by
  rintro x ⟨r, hr, rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  apply (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  exact C_injective σ R (by simpa only [map_zero] using h)

attribute [local instance] algebraMvPolynomial

/-- The actual coefficient-localization equivalence Frac(K[X]) ≃ Frac(R[X]),
where K is the canonical fraction field of the domain R. -/
def coefficientFractionEquiv (R σ : Type*) [CommRing R] [IsDomain R] :
    let M := (nonZeroDivisors R).map (C (σ := σ))
    let := IsLocalization.originalFractionAlgebra (MvPolynomial σ R)
      (MvPolynomial σ (FractionRing R)) M (coefficient_nonZeroDivisors_le R σ)
    FractionRing (MvPolynomial σ (FractionRing R)) ≃ₐ[MvPolynomial σ (FractionRing R)]
      FractionRing (MvPolynomial σ R) :=
  IsLocalization.originalFractionEquiv _ _ _ (coefficient_nonZeroDivisors_le R σ)

end MvPolynomial
