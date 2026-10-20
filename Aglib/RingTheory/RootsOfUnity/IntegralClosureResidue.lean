/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.IntegralClosure.Inertia
public import Aglib.RingTheory.RootsOfUnity.DVR
public import Aglib.RingTheory.RootsOfUnity.BaseField
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Root reduction through a chosen integral-closure prime

Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.IntegralClosureResidue`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section

namespace Field.absoluteGaloisGroup.RootsOfUnity.IntegralClosureResidue

open Field.absoluteGaloisGroup.RootsOfUnity integralClosure.Inertia

universe u v
variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K]
variable (Q : Ideal (IntegralModel R K)) [Q.IsMaximal]
  [Q.LiesOver (IsLocalRing.maximalIdeal R)]

/-- The actual residue extension over the DVR closed point. -/
abbrev ResidueExtension := IntegralModel R K ⧸ Q

/-- The ring homomorphism induced by the actual lying-over diagram. -/
def residueMap : IsLocalRing.ResidueField R →+* ResidueExtension R K Q :=
  algebraMap (R ⧸ IsLocalRing.maximalIdeal R) (IntegralModel R K ⧸ Q)

omit [Q.IsMaximal] in
@[simp]
theorem residueMap_residue (x : R) :
    residueMap R K Q (IsLocalRing.residue R x) =
      Ideal.Quotient.mk Q (algebraMap R (IntegralModel R K) x) := rfl

/-- A field homomorphism into the nonzero residue extension is injective. -/
theorem residueMap_injective : Function.Injective (residueMap R K Q) :=
  (residueMap R K Q).injective

/-- The induced map on actual residue-field units. -/
def residueUnitsMap : (IsLocalRing.ResidueField R)ˣ →* (ResidueExtension R K Q)ˣ :=
  Units.map (residueMap R K Q).toMonoidHom

/-- The actual map from base residue roots into roots in the residue extension. -/
def residueRootsMap (n : ℕ) : rootsOfUnity n (IsLocalRing.ResidueField R) →*
    rootsOfUnity n (ResidueExtension R K Q) :=
  restrictRootsOfUnity (residueMap R K Q) n

/-- Additive form of the actual base residue root map. -/
def residueRootMap (n : ℕ) : Additive (rootsOfUnity n (IsLocalRing.ResidueField R)) →+
    Additive (rootsOfUnity n (ResidueExtension R K Q)) :=
  (residueRootsMap R K Q n).toAdditive

theorem residueRootMap_injective (n : ℕ) : Function.Injective (residueRootMap R K Q n) := by
  intro x y h
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  apply residueMap_injective R K Q
  exact congrArg (fun z : Additive (rootsOfUnity n (ResidueExtension R K Q)) =>
    ((z.toMul : (ResidueExtension R K Q)ˣ) : ResidueExtension R K Q)) h

/-- A root and its inverse are integral, so the root is an actual integral-model unit. -/
def rootIntegralUnit (n : ℕ) (hn : 0 < n) (ζ : Mu K n) : (IntegralModel R K)ˣ where
  val := rootElement R K n hn ζ
  inv := rootElement R K n hn (-ζ)
  val_inv := by
    apply Subtype.ext
    simp [rootElement]
  inv_val := by
    apply Subtype.ext
    simp [rootElement]

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[simp]
theorem rootIntegralUnit_val (n : ℕ) (hn : 0 < n) (ζ : Mu K n) :
    (rootIntegralUnit R K n hn ζ : IntegralModel R K) = rootElement R K n hn ζ := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[simp]
theorem rootIntegralUnit_pow (n : ℕ) (hn : 0 < n) (ζ : Mu K n) :
    rootIntegralUnit R K n hn ζ ^ n = 1 := by
  apply Units.ext
  exact rootElement_pow R K n hn ζ

/-- Roots reduced as actual units modulo the selected maximal ideal. -/
def reducedRoots (n : ℕ) (hn : 0 < n) : rootsOfUnity n (AlgebraicClosure K) →*
    rootsOfUnity n (ResidueExtension R K Q) where
  toFun ζ := ⟨Units.map (Ideal.Quotient.mk Q).toMonoidHom
    (rootIntegralUnit R K n hn (Additive.ofMul ζ)), by
      rw [mem_rootsOfUnity, ← map_pow, rootIntegralUnit_pow, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change Ideal.Quotient.mk Q (rootElement R K n hn 0) = 1
    have h : rootElement R K n hn (0 : Mu K n) = 1 := by ext; rfl
    rw [h, map_one]
  map_mul' ζ ξ := by
    apply Subtype.ext
    apply Units.ext
    change Ideal.Quotient.mk Q (rootElement R K n hn (Additive.ofMul (ζ * ξ))) =
      Ideal.Quotient.mk Q (rootElement R K n hn (Additive.ofMul ζ)) *
        Ideal.Quotient.mk Q (rootElement R K n hn (Additive.ofMul ξ))
    rw [← map_mul]
    congr 1

/-- Actual root reduction, with no choice of primitive roots. -/
def rootReduction (n : ℕ) (hn : 0 < n) : Mu K n →+
    Additive (rootsOfUnity n (ResidueExtension R K Q)) :=
  (reducedRoots R K Q n hn).toAdditive

omit [IsDomain R] [IsDiscreteValuationRing R] [Q.IsMaximal]
  [Q.LiesOver (IsLocalRing.maximalIdeal R)] in
@[simp]
theorem rootReduction_value (n : ℕ) (hn : 0 < n) (ζ : Mu K n) :
    (((rootReduction R K Q n hn ζ).toMul : (ResidueExtension R K Q)ˣ) :
      ResidueExtension R K Q) = Ideal.Quotient.mk Q (rootElement R K n hn ζ) := rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [Q.LiesOver (IsLocalRing.maximalIdeal R)] in
/-- Distinct roots stay distinct after actual reduction when n is invertible in R. -/
theorem rootReduction_injective (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R)) :
    Function.Injective (rootReduction R K Q n hn) := by
  intro x y h
  have hnB : IsUnit (n : IntegralModel R K) := by
    simpa using hnunit.map (algebraMap R (IntegralModel R K))
  have hres := congrArg (fun z : Additive (rootsOfUnity n (ResidueExtension R K Q)) =>
    ((z.toMul : (ResidueExtension R K Q)ˣ) : ResidueExtension R K Q)) h
  have heq := root_eq_of_residue_eq Q n (Ideal.notMem_of_isUnit Q hnB)
    (rootElement_pow R K n hn x) (rootElement_pow R K n hn y) hres
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun z : IntegralModel R K => (z : AlgebraicClosure K)) heq


omit [IsDomain R] [IsDiscreteValuationRing R] [Q.LiesOver (IsLocalRing.maximalIdeal R)] in
/-- Root reduction is bijective: there are exactly n roots in the algebraic
closure, at most n in the residue extension, and none collide under reduction. -/
theorem rootReduction_bijective (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R)) :
    Function.Bijective (rootReduction R K Q n hn) := by
  let : NeZero n := ⟨hn.ne'⟩
  let : NeZero (n : K) := ⟨(show IsUnit (n : K) from by
    simpa using hnunit.map (algebraMap R K)).ne_zero⟩
  apply (rootReduction_injective R K Q n hn hnunit).bijective_of_nat_card_le
  change Nat.card (rootsOfUnity n (ResidueExtension R K Q)) ≤
    Nat.card (rootsOfUnity n (AlgebraicClosure K))
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure K) n]
  exact card_rootsOfUnity (ResidueExtension R K Q) n

/-- Actual root reduction as a proved additive isomorphism. -/
def rootReductionEquiv (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R)) :
    Mu K n ≃+ Additive (rootsOfUnity n (ResidueExtension R K Q)) :=
  AddEquiv.ofBijective (rootReduction R K Q n hn) (rootReduction_bijective R K Q n hn hnunit)

/-- Lift a root in the actual DVR residue field via the actual residue extension. -/
def residueLift (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R)) :
    Additive (rootsOfUnity n (IsLocalRing.ResidueField R)) →+ Mu K n :=
  (rootReductionEquiv R K Q n hn hnunit).symm.toAddMonoidHom.comp (residueRootMap R K Q n)

/-- The lifted root has precisely the prescribed residue. -/
@[simp]
theorem rootReduction_residueLift (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (x : Additive (rootsOfUnity n (IsLocalRing.ResidueField R))) :
    rootReduction R K Q n hn (residueLift R K Q n hn hnunit x) =
      residueRootMap R K Q n x :=
  (rootReductionEquiv R K Q n hn hnunit).apply_symm_apply _

/-- Distinct base residue roots have distinct canonical lifts. -/
theorem residueLift_injective (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R)) :
    Function.Injective (residueLift R K Q n hn hnunit) :=
  (rootReductionEquiv R K Q n hn hnunit).symm.injective.comp (residueRootMap_injective R K Q n)

variable [IsFractionRing R K]

/-- A base-field root inside the integral model is the image of its genuine DVR-unit lift. -/
theorem rootElement_baseRoot (n : ℕ) (hn : 0 < n) (ζ : rootsOfUnity n K) :
    rootElement R K n hn (baseRoot K n ζ) =
      algebraMap R (IntegralModel R K) ((IsDiscreteValuationRing.RootsOfUnity.rootLift R K hn ζ
        : Rˣ) : R) := by
  apply Subtype.ext
  have h := congrArg (fun u : Kˣ => (u : K))
    (IsDiscreteValuationRing.RootsOfUnity.fractionUnits_rootLift R K hn ζ)
  change algebraMap R K ((IsDiscreteValuationRing.RootsOfUnity.rootLift R K hn ζ : Rˣ) : R) =
    ((ζ : Kˣ) : K) at h
  change algebraMap K (AlgebraicClosure K) ((ζ : Kˣ) : K) =
    algebraMap R (AlgebraicClosure K) ((IsDiscreteValuationRing.RootsOfUnity.rootLift R K hn ζ :
      Rˣ) : R)
  rw [IsScalarTower.algebraMap_apply R K (AlgebraicClosure K), h]

omit [Q.IsMaximal] in
/-- Actual root reduction agrees with the canonical residue root used by the tame symbol. -/
theorem rootReduction_baseRoot (n : ℕ) (hn : 0 < n) (ζ : rootsOfUnity n K) :
    rootReduction R K Q n hn (baseRoot K n ζ) =
      residueRootMap R K Q n (Additive.ofMul (IsDiscreteValuationRing.RootsOfUnity.residueRoot R
        K hn ζ)) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change Ideal.Quotient.mk Q (rootElement R K n hn (baseRoot K n ζ)) =
    residueMap R K Q (IsLocalRing.residue R ((IsDiscreteValuationRing.RootsOfUnity.rootLift R K
      hn ζ : Rˣ) : R))
  rw [rootElement_baseRoot, residueMap_residue]

/-- Lifting the actual tame residue root recovers the original base-field root. -/
@[simp]
theorem residueLift_residueRoot (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (ζ : rootsOfUnity n K) :
    residueLift R K Q n hn hnunit (Additive.ofMul
      (IsDiscreteValuationRing.RootsOfUnity.residueRoot R K hn ζ)) =
      baseRoot K n ζ := by
  apply rootReduction_injective R K Q n hn hnunit
  rw [rootReduction_residueLift, rootReduction_baseRoot]

end Field.absoluteGaloisGroup.RootsOfUnity.IntegralClosureResidue
