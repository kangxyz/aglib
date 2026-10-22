/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.FiniteBaseLocalization
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Generators and quotient triangles for actual base localization

These results apply before module finiteness is known. They retain the original
finite algebra generators after localizing the coefficient ring at a prime.
-/

@[expose] public section
noncomputable section
universe u v w w'
namespace FiniteBaseLocalization
variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable (p : Ideal R) [p.IsPrime]
section Coefficients

variable (k : Type w) [CommRing k] [Algebra k R] [Algebra k B] [IsScalarTower k R B]

instance coefficientBaseTower : IsScalarTower k R (BaseLocalized (B := B) p) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  simp only [IsScalarTower.algebraMap_apply k B (BaseLocalized (B := B) p),
    IsScalarTower.algebraMap_apply k R B,
    IsScalarTower.algebraMap_apply R B (BaseLocalized (B := B) p)]

instance coefficientLocalizedTower :
    IsScalarTower k (Localization.AtPrime p) (BaseLocalized (B := B) p) := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rw [IsScalarTower.algebraMap_apply k R (BaseLocalized (B := B) p),
    IsScalarTower.algebraMap_apply k R (Localization.AtPrime p),
    IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (BaseLocalized (B := B) p)]

/-- Every original algebra generator survives as a generator over the localized coefficient ring. -/
theorem adjoin_range_eq_top {ι : Type w'} (z : ι → B)
    (hz : Algebra.adjoin k (Set.range z) = ⊤) :
    Algebra.adjoin (Localization.AtPrime p)
      (Set.range (fun i => algebraMap B (BaseLocalized (B := B) p) (z i))) = ⊤ := by
  let C := Algebra.adjoin (Localization.AtPrime p)
    (Set.range (fun i => algebraMap B (BaseLocalized (B := B) p) (z i)))
  have hnum : ∀ b : B, algebraMap B (BaseLocalized (B := B) p) b ∈ C := by
    let D := (C.restrictScalars k).comap (IsScalarTower.toAlgHom k B (BaseLocalized (B := B) p))
    have hle : Algebra.adjoin k (Set.range z) ≤ D := by
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    intro b
    exact hle (by rw [hz]; trivial)
  apply top_unique
  intro x _
  obtain ⟨b, d, rfl⟩ := IsLocalization.exists_mk'_eq
    (Algebra.algebraMapSubmonoid B (p.primeCompl)) x
  rcases d with ⟨d, r, hr, rfl⟩
  have heq : IsLocalization.mk' (BaseLocalized (B := B) p) b
      ⟨algebraMap R B r, Algebra.mem_algebraMapSubmonoid_of_mem ⟨r, hr⟩⟩ =
      algebraMap B (BaseLocalized (B := B) p) b *
        algebraMap (Localization.AtPrime p) (BaseLocalized (B := B) p)
          (IsLocalization.mk' (Localization.AtPrime p) 1 ⟨r, hr⟩) := by
    rw [IsLocalization.algebraMap_mk' B, map_one,
      IsLocalization.mk'_eq_mul_mk'_one]
  rw [heq]
  exact C.mul_mem (hnum b) (C.algebraMap_mem _)

/-- Genuine finite type over the smaller coefficient ring suffices after base localization. -/
theorem finiteType [Algebra.FiniteType k B] :
    Algebra.FiniteType (Localization.AtPrime p) (BaseLocalized (B := B) p) := by
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
  refine ⟨⟨s.image (algebraMap B (BaseLocalized (B := B) p)), ?_⟩⟩
  have himage : Set.range (fun b : s => algebraMap B (BaseLocalized (B := B) p) (b : B)) =
      (algebraMap B (BaseLocalized (B := B) p)) '' (s : Set B) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [Finset.coe_image, ← himage]
  exact adjoin_range_eq_top p k (fun b : s => (b : B)) hz

end Coefficients

/-- The literal quotient map induced by the localization map. -/
def quotientMap (q : Ideal B) : B ⧸ q →+* BaseLocalized (B := B) p ⧸ selectedPrime p q :=
  Ideal.quotientMap (selectedPrime p q) (algebraMap B (BaseLocalized (B := B) p))
    Ideal.le_comap_map

@[simp] theorem quotientMap_mk (q : Ideal B) (b : B) :
    quotientMap p q (Ideal.Quotient.mk q b) =
      Ideal.Quotient.mk (selectedPrime p q) (algebraMap B (BaseLocalized (B := B) p) b) := rfl

/-- The coefficient square uses the actual localization and quotient maps. -/
theorem quotientMap_comp_algebraMap (q : Ideal B) :
    (algebraMap (Localization.AtPrime p) (BaseLocalized (B := B) p ⧸ selectedPrime p q)).comp
        (algebraMap R (Localization.AtPrime p)) =
      (quotientMap p q).comp (algebraMap R (B ⧸ q)) := by
  ext r
  change algebraMap (Localization.AtPrime p) (BaseLocalized (B := B) p ⧸ selectedPrime p q)
      (algebraMap R (Localization.AtPrime p) r) = _
  rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p)
    (BaseLocalized (B := B) p ⧸ selectedPrime p q)]
  change Ideal.Quotient.mk (selectedPrime p q) (algebraMap R (BaseLocalized (B := B) p) r) =
    quotientMap p q (Ideal.Quotient.mk q (algebraMap R B r))
  rw [quotientMap_mk, IsScalarTower.algebraMap_apply R B (BaseLocalized (B := B) p)]

end FiniteBaseLocalization
