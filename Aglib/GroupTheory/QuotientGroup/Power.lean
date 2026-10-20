/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Power maps on quotients by cyclic subgroups

The ambient power-surjectivity premise is retained for arbitrary groups.
For units of an algebraically closed field it is proved; the cardinality
formulas retain characteristic zero and infinite-order period hypotheses.

Source: `R5Lab.Aglib.GroupTheory.QuotientGroup.Power`.
Packet SHA-256:
`30e23df4f0618ba0362ca0be34f9414049955e6983deec51e0405ee24cadfffd`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
namespace QuotientGroup
universe u v
section Lattice

variable {G : Type u} [CommGroup G]


/-- A power relation sends the source period lattice into the target lattice. -/
theorem zpowers_le_comap_pow (p q : G) (a b : ℕ) (h : p ^ a = q ^ b) :
    Subgroup.zpowers p ≤ (Subgroup.zpowers q).comap (powMonoidHom a) := by
  apply Subgroup.zpowers_le.mpr
  change p ^ a ∈ Subgroup.zpowers q
  rw [h]
  exact Subgroup.npow_mem_zpowers q b

/-- The map is induced by x ↦ x^a on actual units, not supplied separately. -/
def zpowersPowerMap (p q : G) (a b : ℕ) (h : p ^ a = q ^ b) :
    (G ⧸ Subgroup.zpowers p) →* (G ⧸ Subgroup.zpowers q) :=
  QuotientGroup.map _ _ (powMonoidHom a) (zpowers_le_comap_pow p q a b h)

@[simp] theorem zpowersPowerMap_mk (p q : G) (a b : ℕ) (h : p ^ a = q ^ b)
    (x : G) : zpowersPowerMap p q a b h (QuotientGroup.mk x) =
      QuotientGroup.mk (x ^ a) := rfl

/-- The source lattice has trivial intersection with the power kernel. -/
theorem zpowers_inf_pow_ker (p : G) (a : ℕ) (ha : 0 < a)
    (hp : orderOf p = 0) :
    Subgroup.zpowers p ⊓ (powMonoidHom (α := G) a).ker = ⊥ := by
  apply le_antisymm _ bot_le
  rintro x ⟨hx, hk⟩
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  change (p ^ z) ^ a = 1 at hk
  have hz : p ^ (z * (a : ℤ)) = p ^ (0 : ℤ) := by
    simpa only [zpow_mul, zpow_natCast, zpow_zero] using hk
  have hz' : z * (a : ℤ) = 0 :=
    (injective_zpow_iff_not_isOfFinOrder.mpr (orderOf_eq_zero_iff.mp hp)) hz
  have hz0 : z = 0 := (mul_eq_zero.mp hz').resolve_right (by omega)
  simp [hz0]

/-- The exact lattice-index computation. No cardinality or degree of the
quotient map is assumed. The ambient power map is assumed surjective; over an
algebraically closed field this is proved below. -/
theorem zpowersPowerMap_kernel_card (p q : G) (a b : ℕ)
    (ha : 0 < a) (hp : orderOf p = 0) (hq : orderOf q = 0)
    (h : p ^ a = q ^ b) (hs : Function.Surjective (powMonoidHom (α := G) a)) :
    Nat.card (zpowersPowerMap p q a b h).ker =
      Nat.card (powMonoidHom (α := G) a).ker * b := by
  let H := Subgroup.zpowers p
  let J := Subgroup.zpowers q
  let f : G →* G := powMonoidHom a
  let M := J.comap f
  have hHM : H ≤ M := zpowers_le_comap_pow p q a b h
  have hKM : f.ker ≤ M := by
    intro x hx
    change f x ∈ J
    rw [show f x = 1 from hx]
    exact J.one_mem
  have hfirst : H.relIndex (H ⊔ f.ker) = Nat.card f.ker := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right,
      show H ⊓ f.ker = ⊥ from zpowers_inf_pow_ker p a ha hp,
      Subgroup.relIndex_bot_left]
  have hsecond : (H ⊔ f.ker).relIndex M = b := by
    have hmap : H.map f = Subgroup.zpowers (q ^ b) := by
      rw [show H = Subgroup.zpowers p from rfl, MonoidHom.map_zpowers]
      exact congrArg Subgroup.zpowers h
    have hmapM : M.map f = J := Subgroup.map_comap_eq_self_of_surjective hs J
    have heq := Subgroup.relIndex_map_map f H M
    rw [sup_of_le_left hKM, hmap, hmapM] at heq
    rw [← heq]
    change (Subgroup.zpowers (q ^ b)).relIndex (Subgroup.zpowers q) = b
    simpa [hq] using Subgroup.relIndex_zpowers_zpow q (b : ℤ)
  have hcard : Nat.card (zpowersPowerMap p q a b h).ker = H.relIndex M := by
    rw [zpowersPowerMap, QuotientGroup.ker_map]
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [hcard, ← Subgroup.relIndex_mul_relIndex H (H ⊔ f.ker) M
    le_sup_left (sup_le hHM hKM), hfirst, hsecond]

end Lattice

section Field

variable (K : Type u) [Field K] [hK : IsAlgClosed K]

/-- Surjectivity of x ↦ x^a on the actual units of an algebraically closed field. -/
theorem units_pow_surjective (a : ℕ) (ha : 0 < a) :
    Function.Surjective (powMonoidHom (α := Kˣ) a) := by
  intro x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : K) ha
  have hy0 : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_pow (by omega)] at hy
    exact x.ne_zero hy.symm
  refine ⟨Units.mk0 y hy0, ?_⟩
  apply Units.ext
  exact hy

omit hK in
/-- The power kernel is exactly the standard roots-of-unity subgroup.
The algebraic-closedness input of the source interface is retained. -/
@[nolint unusedArguments]
theorem units_pow_ker [IsAlgClosed K] (a : ℕ) :
    (powMonoidHom (α := Kˣ) a).ker = rootsOfUnity a K := by
  ext x
  simp [MonoidHom.mem_ker, mem_rootsOfUnity]

/-- All geometric quotient fibres have the expected size a*b. The use of
characteristic zero occurs in the cardinality of the actual a-th roots of unity. -/
theorem zpowersPowerMap_units_kernel_card [CharZero K] (p q : Kˣ) (a b : ℕ)
    (ha : 0 < a) (hp : orderOf p = 0) (hq : orderOf q = 0)
    (h : p ^ a = q ^ b) :
    Nat.card (zpowersPowerMap p q a b h).ker = a * b := by
  let : NeZero a := ⟨by omega⟩
  rw [zpowersPowerMap_kernel_card p q a b ha hp hq h
    (units_pow_surjective K a ha), units_pow_ker,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity]

/-- The quotient power map is surjective over an algebraically closed field. -/
theorem zpowersPowerMap_units_surjective (p q : Kˣ) (a b : ℕ)
    (ha : 0 < a) (h : p ^ a = q ^ b) :
    Function.Surjective (zpowersPowerMap p q a b h) := by
  apply QuotientGroup.map_surjective_of_surjective
  exact (QuotientGroup.mk'_surjective (Subgroup.zpowers q)).comp
    (units_pow_surjective K a ha)

/-- Every fibre of the literal geometric lattice map has a*b elements.
This is not yet the scheme-theoretic `HasGeometricDegree` assertion. -/
theorem zpowersPowerMap_units_fibre_card [CharZero K] (p q : Kˣ) (a b : ℕ)
    (ha : 0 < a) (hp : orderOf p = 0) (hq : orderOf q = 0)
    (h : p ^ a = q ^ b) (y : (Kˣ ⧸ Subgroup.zpowers q)) :
    Nat.card {x : (Kˣ ⧸ Subgroup.zpowers p) // zpowersPowerMap p q a b h x = y} = a * b := by
  calc
    _ = Nat.card (zpowersPowerMap p q a b h).ker :=
      Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective
        (zpowersPowerMap_units_surjective K p q a b ha h) y)
    _ = a * b := zpowersPowerMap_units_kernel_card K p q a b ha hp hq h

end Field


section SignedLattice

variable {G : Type u} [CommGroup G]

/-- The actual signed power map on multiplicative period quotients. -/
def zpowersSignedPowerMap (p q : G) (a b : ℤ) (h : p ^ a = q ^ b) :
    (G ⧸ Subgroup.zpowers p) →* (G ⧸ Subgroup.zpowers q) :=
  QuotientGroup.map _ _ (zpowGroupHom a) (Subgroup.zpowers_le.mpr (by
    change p ^ a ∈ Subgroup.zpowers q
    rw [h]
    exact Subgroup.zpow_mem_zpowers q b))

/-- Simultaneous inversion uses this actual source-group automorphism. -/
def zpowersInversion (p : G) : (G ⧸ Subgroup.zpowers p) ≃* (G ⧸ Subgroup.zpowers p) where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' := mul_inv

/-- The source inversion commutes with the fixed target map after simultaneous
negation of both exponents. This is proved on literal quotient representatives. -/
theorem zpowersSignedPowerMap_neg (p q : G) (a b : ℤ) (h : p ^ a = q ^ b) :
    (zpowersSignedPowerMap p q (-a) (-b)
      (by simpa only [zpow_neg] using congrArg Inv.inv h)).comp
        (zpowersInversion p).toMonoidHom = zpowersSignedPowerMap p q a b h := by
  apply QuotientGroup.monoidHom_ext
  ext x
  simp [zpowersSignedPowerMap, zpowersInversion, zpow_neg]

end SignedLattice
end QuotientGroup
