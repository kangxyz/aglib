/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Aglib.RepresentationTheory.EquivariantQuotients

/-!
This module retains the assigned finite coefficient declarations.
The original source context below describes the full pre-split family;
its stated hypotheses and uninstantiated comparison boundaries remain in force.
-/

@[expose] public section

/-!
# Finite cyclic Tate coefficients

Source: `K2-018#eq:k2018-coefficient-compatibility` (lines 292–306) and
`K2-018#prop:k2018-arithmetic-characters` (lines 341–445),
`research/exposes/K2/018/expose.tex`, SHA-256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.

At a positive level `n`, the coefficient group is the actual additive group
`ZMod n`. A supplied unit-valued cyclotomic character acts by its square.
Insertion from level `d` to level `n` multiplies integer representatives by
`n / d`; reduction is the separate ring homomorphism in the opposite direction.
The proofs below establish these coefficient maps and their equivariance when
the supplied cyclotomic characters reduce compatibly. They do not construct a
cyclotomic character or a Tate lattice, or assert either Bockstein identity.

For an arbitrary additive group, the exact additive order of a character into
`ZMod n` is the cardinality of its image. Thus exact order `n` is equivalent to
surjectivity. No finiteness or exponent assumption on the domain is needed.
The coefficient automorphisms are exactly multiplication by units, all of which
commute with the supplied Tate action. These are the finite cyclic algebra
steps toward marked rational isogenies; actual elliptic torsion, quotient curves,
continuity and the geometric/cohomological comparison remain uninstantiated.
The transport and conjugate-Hom declarations also give auxiliary algebraic
consequences of these conventions. Their inverse cyclotomic character is
derived in cyclic coordinates, rather than imported as a geometric kernel fact.
Each declaration's source pointer uses the source hash above.
-/

namespace AddMonoidHom.CyclicCharacters

open RepresentationTheory.EquivariantQuotients

variable {d n : ℕ}

variable {V A : Type*} [AddGroup V] [AddCommGroup A]

/-- The exact additive order of an additive character is the exponent of
its image, the auxiliary group step behind primitive characters in
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
No claim is made that every nonzero image element has this exponent. -/
theorem character_order_eq_image_exponent (f : V →+ A) :
    addOrderOf f = AddMonoid.exponent f.range := by
  apply Nat.dvd_antisymm
  · apply addOrderOf_dvd_of_nsmul_eq_zero
    apply AddMonoidHom.ext
    intro v
    exact congrArg Subtype.val
      (AddMonoid.exponent_nsmul_eq_zero (⟨f v, v, rfl⟩ : f.range))
  · apply AddMonoid.exponent_dvd_of_forall_nsmul_eq_zero
    rintro ⟨a, v, rfl⟩
    apply Subtype.ext
    exact DFunLike.congr_fun (addOrderOf_nsmul_eq_zero f) v

/-- A character into the finite cyclic coefficient group has order equal to
the size of its cyclic image, the algebraic primitive-character step of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
Only positivity of the coefficient level is assumed; the domain may be infinite. -/
-- Keep the original nonzero coefficient-level input of this finite cyclic character formula.
@[nolint unusedArguments]
theorem character_order_eq_image_card [NeZero n] (f : V →+ ZMod n) :
    addOrderOf f = Nat.card f.range :=
  (character_order_eq_image_exponent f).trans IsAddCyclic.exponent_eq_card

/-- A character has exact additive order `n` if and only if it is surjective
onto `ZMod n`, the finite cyclic algebra in the primitive-character step of
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
There is no domain finiteness or exponent hypothesis. -/
theorem character_order_eq_level_iff_surjective [NeZero n] (f : V →+ ZMod n) :
    addOrderOf f = n ↔ Function.Surjective f := by
  rw [character_order_eq_image_card]
  have hc : Nat.card f.range = n ↔ Nat.card f.range = Nat.card (ZMod n) := by
    rw [Nat.card_zmod]
  exact hc.trans ((AddSubgroup.card_eq_iff_eq_top f.range).trans f.range_eq_top)

/-- A surjective character on a group of size `n^2` has kernel of size `n`,
the conditional rank-two torsion calculation in the auxiliary algebra for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
The cardinality hypothesis is explicit; no elliptic torsion realization is
asserted. Positivity of `n` makes the domain finite automatically. -/
theorem kernel_card_of_rank_two_card [NeZero n] (f : V →+ ZMod n)
    (hcard : Nat.card V = n ^ 2) (hf : Function.Surjective f) :
    Nat.card f.ker = n := by
  have hindex : f.ker.index = n := by
    rw [AddSubgroup.index_ker, f.range_eq_top.mpr hf, AddSubgroup.card_top, Nat.card_zmod]
  have hc := f.ker.card_mul_index
  rw [hindex, hcard, pow_two] at hc
  exact Nat.eq_of_mul_eq_mul_right (NeZero.pos n) hc

/-- The preceding kernel-size calculation for the concrete rank-two
additive model `ZMod n × ZMod n`, an auxiliary finite-group corollary for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
This does not identify the model with `E[n]`. -/
theorem rank_two_kernel_card [NeZero n]
    (f : ZMod n × ZMod n →+ ZMod n) (hf : Function.Surjective f) :
    Nat.card f.ker = n :=
  kernel_card_of_rank_two_card f (by simp [pow_two]) hf

/-- Multiplication by a coefficient unit as an additive marking, the
concrete coefficient-automorphism model for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
This is an additive automorphism, not a ring automorphism. -/
def unitMarking (u : (ZMod n)ˣ) : ZMod n ≃+ ZMod n :=
  (ZMod.AddAutEquivUnits n).symm (Additive.ofMul u)

/-- Formula for multiplication by a coefficient unit in the auxiliary
marking algebra for `K2-018#prop:k2018-arithmetic-characters`, on the module
source basis. -/
@[simp]
theorem unitMarking_apply (u : (ZMod n)ˣ) (a : ZMod n) :
    unitMarking u a = (u : ZMod n) * a := rfl

/-- Every additive coefficient automorphism is multiplication by a unit,
the auxiliary marking-forgetting step for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis. -/
theorem addEquiv_eq_unitMarking (e : ZMod n ≃+ ZMod n) :
    unitMarking ((ZMod.AddAutEquivUnits n e).toMul) = e :=
  (ZMod.AddAutEquivUnits n).symm_apply_apply e

/-- An additive endomorphism of a cyclic coefficient group is multiplication
by its value at `1`, the auxiliary coefficient algebra for
`K2-018#prop:k2018-arithmetic-characters`, on the module source basis.
This does not assert that a general character has image generated by every
nonzero value. -/
theorem addHom_apply_eq_mul (f : ZMod n →+ ZMod n) (a : ZMod n) :
    f a = f 1 * a := by
  symm
  rw [mul_comm, ← a.intCast_zmod_cast, ← zsmul_eq_mul, ← map_zsmul, zsmul_one]

end AddMonoidHom.CyclicCharacters

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 1a28884bcfcbabef06564b3868de2c08b799c26a4698f803f9066f566ad2be7d.
Definitions, hypotheses and universes are retained modulo native names. -/
