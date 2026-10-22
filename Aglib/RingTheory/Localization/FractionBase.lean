/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Fraction-base localization of an algebra

For a domain `R` and an `R`-algebra `B`, invert in `B` the images of the nonzero
base elements. The resulting algebra carries the actual localized action of
`FractionRing R`; no fraction-field action on `B` is required. Algebra generators
over a smaller coefficient ring remain generators over this fraction field.
A prime with zero contraction extends to the localization, with the expected
prime-local equivalence and the literal quotient-map square.
-/

@[expose] public section

noncomputable section

universe u v w w'

namespace FractionBaseLocalization

variable (R : Type u) [CommRing R] [IsDomain R]
variable (B : Type v) [CommRing B] [Algebra R B]

/-- Localization of the algebra at the actual image of the base nonzero elements. -/
abbrev BaseLocalized := Localization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))

/-- The fraction-field action is the native map between the two localizations. -/
instance fractionAlgebra : Algebra (FractionRing R) (BaseLocalized R B) := inferInstance

instance fractionTower : IsScalarTower R (FractionRing R) (BaseLocalized R B) := inferInstance

section Coefficients

variable (k : Type w) [CommRing k] [Algebra k R] [Algebra k B] [IsScalarTower k R B]

instance coefficientBaseTower : IsScalarTower k R (BaseLocalized R B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  simp only [IsScalarTower.algebraMap_apply k B (BaseLocalized R B),
    IsScalarTower.algebraMap_apply k R B,
    IsScalarTower.algebraMap_apply R B (BaseLocalized R B)]

instance coefficientFractionTower :
    IsScalarTower k (FractionRing R) (BaseLocalized R B) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [IsScalarTower.algebraMap_apply k R (BaseLocalized R B),
    IsScalarTower.algebraMap_apply k R (FractionRing R),
    IsScalarTower.algebraMap_apply R (FractionRing R) (BaseLocalized R B)]

/-- Every original algebra generator survives as a generator over the fraction base. -/
theorem adjoin_range_eq_top {ι : Type w'} (z : ι → B)
    (hz : Algebra.adjoin k (Set.range z) = ⊤) :
    Algebra.adjoin (FractionRing R)
      (Set.range (fun i => algebraMap B (BaseLocalized R B) (z i))) = ⊤ := by
  let C := Algebra.adjoin (FractionRing R)
    (Set.range (fun i => algebraMap B (BaseLocalized R B) (z i)))
  have hnum : ∀ b : B, algebraMap B (BaseLocalized R B) b ∈ C := by
    let D := (C.restrictScalars k).comap (IsScalarTower.toAlgHom k B (BaseLocalized R B))
    have hle : Algebra.adjoin k (Set.range z) ≤ D := by
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    intro b
    exact hle (by rw [hz]; trivial)
  apply top_unique
  intro x _
  obtain ⟨b, d, rfl⟩ := IsLocalization.exists_mk'_eq
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) x
  rcases d with ⟨d, r, hr, rfl⟩
  have hrF : algebraMap R (FractionRing R) r ≠ 0 := by
    exact fun h => nonZeroDivisors.ne_zero hr
      ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
  have heq : IsLocalization.mk' (BaseLocalized R B) b
      ⟨algebraMap R B r, Algebra.mem_algebraMapSubmonoid_of_mem ⟨r, hr⟩⟩ =
      algebraMap B (BaseLocalized R B) b *
        algebraMap (FractionRing R) (BaseLocalized R B)
          ((algebraMap R (FractionRing R) r)⁻¹) := by
    apply IsLocalization.mk'_eq_iff_eq_mul.mpr
    change algebraMap B (BaseLocalized R B) b =
      (algebraMap B (BaseLocalized R B) b *
        algebraMap (FractionRing R) (BaseLocalized R B)
          ((algebraMap R (FractionRing R) r)⁻¹)) *
        algebraMap B (BaseLocalized R B) (algebraMap R B r)
    rw [← IsScalarTower.algebraMap_apply R B (BaseLocalized R B),
      IsScalarTower.algebraMap_apply R (FractionRing R) (BaseLocalized R B),
      mul_assoc, ← map_mul, inv_mul_cancel₀ hrF, map_one, mul_one]
  rw [heq]
  exact C.mul_mem (hnum b) (C.algebraMap_mem _)

/-- Genuine finite type over the smaller coefficient ring suffices after base localization. -/
theorem finiteType [Algebra.FiniteType k B] :
    Algebra.FiniteType (FractionRing R) (BaseLocalized R B) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k B).out
  have hsrange : Set.range (fun b : s => (b : B)) = (s : Set B) := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact a.property
    · intro hb
      exact ⟨⟨b, hb⟩, rfl⟩
  have hz : Algebra.adjoin k (Set.range (fun b : s => (b : B))) = ⊤ := by
    rw [hsrange]
    exact hs
  refine ⟨⟨s.image (algebraMap B (BaseLocalized R B)), ?_⟩⟩
  have himage : Set.range (fun b : s => algebraMap B (BaseLocalized R B) (b : B)) =
      (algebraMap B (BaseLocalized R B)) '' (s : Set B) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [Finset.coe_image, ← himage]
  exact adjoin_range_eq_top R B k (fun b : s => (b : B)) hz

end Coefficients

/-- The selected prime is the actual extension of the original ideal. -/
def selectedPrime (q : Ideal B) : Ideal (BaseLocalized R B) :=
  q.map (algebraMap B (BaseLocalized R B))

theorem disjoint_nonZeroDivisors (q : Ideal B)
    (hq : q.comap (algebraMap R B) = ⊥) :
    Disjoint (Algebra.algebraMapSubmonoid B (nonZeroDivisors R) : Set B) (q : Set B) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨r, hr, rfl⟩ hmem
  have h : r ∈ q.comap (algebraMap R B) := hmem
  rw [hq] at h
  exact nonZeroDivisors.ne_zero hr h

theorem selectedPrime_isPrime (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap R B) = ⊥) : (selectedPrime R B q).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (BaseLocalized R B)
    q inferInstance (disjoint_nonZeroDivisors R B q hq)

theorem selectedPrime_comap (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap R B) = ⊥) :
    (selectedPrime R B q).comap (algebraMap B (BaseLocalized R B)) = q :=
  IsLocalization.under_map_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (BaseLocalized R B)
    inferInstance (disjoint_nonZeroDivisors R B q hq)

/-- Localizing at the selected prime is canonically the original prime localization. -/
def localEquiv (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap R B) = ⊥) :
    letI := selectedPrime_isPrime R B q hq
    Localization.AtPrime (selectedPrime R B q) ≃ₐ[B] Localization.AtPrime q := by
  letI := selectedPrime_isPrime R B q hq
  letI : IsLocalization.AtPrime (Localization.AtPrime (selectedPrime R B q)) q := by
    have h : IsLocalization.AtPrime (Localization.AtPrime (selectedPrime R B q))
        ((selectedPrime R B q).comap (algebraMap B (BaseLocalized R B))) := inferInstance
    have hM :
        ((selectedPrime R B q).comap (algebraMap B (BaseLocalized R B))).primeCompl =
          q.primeCompl := by
      ext b
      change b ∉ (selectedPrime R B q).comap (algebraMap B (BaseLocalized R B)) ↔ b ∉ q
      rw [selectedPrime_comap R B q hq]
    exact Eq.mp (congrArg
      (fun M : Submonoid B => IsLocalization M
        (Localization.AtPrime (selectedPrime R B q))) hM) h
  exact IsLocalization.algEquiv q.primeCompl _ _

theorem localEquiv_algebraMap (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap R B) = ⊥) (b : B) :
    letI := selectedPrime_isPrime R B q hq
    localEquiv R B q hq
      (algebraMap B (Localization.AtPrime (selectedPrime R B q)) b) =
      algebraMap B (Localization.AtPrime q) b := by
  let := selectedPrime_isPrime R B q hq
  exact (localEquiv R B q hq).commutes b

/-- The literal quotient map induced by the localization map. -/
def quotientMap (q : Ideal B) : B ⧸ q →+* BaseLocalized R B ⧸ selectedPrime R B q :=
  Ideal.quotientMap (selectedPrime R B q) (algebraMap B (BaseLocalized R B))
    Ideal.le_comap_map

omit [IsDomain R] in
@[simp] theorem quotientMap_mk (q : Ideal B) (b : B) :
    quotientMap R B q (Ideal.Quotient.mk q b) =
      Ideal.Quotient.mk (selectedPrime R B q) (algebraMap B (BaseLocalized R B) b) := rfl

omit [IsDomain R] in
/-- The coefficient square is about the actual localization and quotient maps. -/
theorem quotientMap_comp_algebraMap (q : Ideal B) :
    (algebraMap (FractionRing R) (BaseLocalized R B ⧸ selectedPrime R B q)).comp
        (algebraMap R (FractionRing R)) =
      (quotientMap R B q).comp (algebraMap R (B ⧸ q)) := by
  ext r
  change algebraMap (FractionRing R) (BaseLocalized R B ⧸ selectedPrime R B q)
      (algebraMap R (FractionRing R) r) = _
  rw [← IsScalarTower.algebraMap_apply R (FractionRing R)
    (BaseLocalized R B ⧸ selectedPrime R B q)]
  change Ideal.Quotient.mk (selectedPrime R B q) (algebraMap R (BaseLocalized R B) r) =
    quotientMap R B q (Ideal.Quotient.mk q (algebraMap R B r))
  rw [quotientMap_mk, IsScalarTower.algebraMap_apply R B (BaseLocalized R B)]

end FractionBaseLocalization
