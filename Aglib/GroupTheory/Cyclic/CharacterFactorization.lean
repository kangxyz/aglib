/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Data.ZMod.CoefficientMaps
public import Aglib.GroupTheory.Cyclic.Characters

/-!
# Factoring a cyclic character at its actual order

The factor is constructed by inverting insertion on its proved range.
No finite-domain, geometric or character-realization premise is introduced.

Source: `R5Lab.Aglib.GroupTheory.Cyclic.CharacterFactorization`.
Packet SHA-256:
`0087748552bcd95578db11f077ca45aa7c184197244d8f2084d820338e70fc75`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

open _root_.AddMonoidHom.CyclicCharacters


namespace AddMonoidHom.CyclicCharacters

open ZMod

variable {d m : ℕ} [NeZero m]
variable {V : Type*} [AddGroup V]

/-- The actual cyclic image equals the divisorInsertion subgroup, proved from the image order and
cyclic subgroup cardinality uniqueness.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem range_eq_divisorInsertion_range (f : V →+ ZMod m) (hd : d ∣ m)
    (ho : addOrderOf f = d) : f.range = (divisorInsertion hd).range := by
  apply IsAddCyclic.addSubgroup_eq_iff_card_eq.2
  calc
    Nat.card f.range = d := (character_order_eq_image_card f).symm.trans ho
    _ = Nat.card (divisorInsertion hd).range :=
      (Nat.card_zmod d).symm.trans
        (Nat.card_congr ((divisorInsertion hd).ofInjective (divisorInsertion_injective hd)).toEquiv)

/-- Construct the unique additive character at its actual order by inverting divisorInsertion on its
proved image range.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
noncomputable def liftAddHom (f : V →+ ZMod m) (hd : d ∣ m)
    (ho : addOrderOf f = d) : V →+ ZMod d :=
  ((divisorInsertion hd).ofInjective (divisorInsertion_injective hd)).symm.toAddMonoidHom.comp
    (f.codRestrict (divisorInsertion hd).range (fun v => by
      rw [← range_eq_divisorInsertion_range f hd ho]
      exact ⟨v, rfl⟩))

/-- Insertion of the constructed level-d character is the original character, pointwise.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
@[simp] theorem divisorInsertion_liftAddHom (f : V →+ ZMod m) (hd : d ∣ m)
    (ho : addOrderOf f = d) (v : V) : divisorInsertion hd (liftAddHom f hd ho v) = f v := by
  exact congrArg Subtype.val
    (((divisorInsertion hd).ofInjective (divisorInsertion_injective hd)).apply_symm_apply
      (f.codRestrict (divisorInsertion hd).range (fun v => by
        rw [← range_eq_divisorInsertion_range f hd ho]
        exact ⟨v, rfl⟩) v))

/-- The constructed actual-image character is surjective onto its level-d coefficients.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem liftAddHom_surjective (f : V →+ ZMod m) (hd : d ∣ m)
    (ho : addOrderOf f = d) : Function.Surjective (liftAddHom f hd ho) := by
  intro a
  have hmem : divisorInsertion hd a ∈ f.range := by
    rw [range_eq_divisorInsertion_range f hd ho]
    exact ⟨a, rfl⟩
  obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.1 hmem
  refine ⟨v, ?_⟩
  apply divisorInsertion_injective hd
  rw [divisorInsertion_liftAddHom]
  exact hv

/-- Insertion injectivity makes the constructed additive factorization unique.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem liftAddHom_unique (f : V →+ ZMod m) (hd : d ∣ m)
    (ho : addOrderOf f = d) (k : V →+ ZMod d)
    (hk : (divisorInsertion hd).comp k = f) : k = liftAddHom f hd ho := by
  ext v
  apply divisorInsertion_injective hd
  rw [divisorInsertion_liftAddHom]
  exact DFunLike.congr_fun hk v

/-- Passing to the actual-image coefficient level preserves the geometric kernel.
Source: the auxiliary actual-image step of
`K2-018#prop:k2018-integrality-test`, lines 667–677, and the primitive-character
step of `K2-018#prop:k2018-arithmetic-characters`, lines 393–442,
at the documented source snapshot. -/
theorem liftAddHom_ker (f : V →+ ZMod m) (hd : d ∣ m)
    (ho : addOrderOf f = d) : (liftAddHom f hd ho).ker = f.ker := by
  ext v
  change liftAddHom f hd ho v = 0 ↔ f v = 0
  constructor
  · intro hv
    rw [← divisorInsertion_liftAddHom f hd ho v, hv, map_zero]
  · intro hv
    apply divisorInsertion_injective hd
    rw [divisorInsertion_liftAddHom, hv, map_zero]

end AddMonoidHom.CyclicCharacters
