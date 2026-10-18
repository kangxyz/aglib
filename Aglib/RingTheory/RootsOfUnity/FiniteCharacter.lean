/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Algebra.Group.Units
public import Aglib.GroupTheory.Cyclic.Characters

/-!
# The finite cyclotomic character of the actual absolute Galois group

Source: the cyclotomic coefficient convention in
`K2-018#eq:k2018-coefficient-compatibility` and
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex`, SHA-256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
The source snapshot applies to every declaration below; this module constructs
the finite coefficient character itself, rather than either Bockstein identity.

For a characteristic-zero field `F` and a positive level `n`, a primitive root
is chosen in the actual `AlgebraicClosure F`. The existing absolute Galois group
is precisely its group of F-algebra automorphisms with the Krull topology.
The root-power exponent homomorphism is proved independent of the chosen
primitive root, and continuity is derived from its Krull-open stabilizer.
Neither a character nor its continuity is supplied as a premise.

This does not construct a coefficient scheme, a scheme fundamental-group
comparison, or an H¹/monodromy realization. Its unit-valued character can be
passed directly to the separately proved scalar coefficient interfaces.
-/

@[expose] public section

namespace Field.absoluteGaloisGroup.CyclotomicCharacter

open Filter Topology

section PrimitiveRoot

variable (F : Type*) [Field F] {n : ℕ} [NeZero n]
  {ζ : AlgebraicClosure F}

/-- The defining algebraic automorphism underlying mathlib's actual
absolute Galois group, exposing evaluation for
`K2-018#eq:k2018-coefficient-compatibility`. This is a definitional view,
not a supplied Galois comparison or an action premise. -/
abbrev asAutomorphism (σ : Field.absoluteGaloisGroup F) :
    AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ

/-- The actual absolute Galois exponent character of a genuine primitive
root, constructing the finite coefficient character in
`K2-018#eq:k2018-coefficient-compatibility`. The only input beyond the field
and positive level is this root, not a character or a prescribed action. -/
noncomputable def fromPrimitiveRoot (hζ : IsPrimitiveRoot ζ n) :
    Field.absoluteGaloisGroup F →* (ZMod n)ˣ :=
  hζ.autToPow F

/-- Primitive-root evaluation for the actual exponent character underlying
`K2-018#eq:k2018-coefficient-compatibility`. The exponent is its residue-class
value represented in `[0,n)`. -/
theorem fromPrimitiveRoot_eval (hζ : IsPrimitiveRoot ζ n)
    (σ : Field.absoluteGaloisGroup F) :
    asAutomorphism F σ ζ = ζ ^ (fromPrimitiveRoot F hζ σ : ZMod n).val :=
  (hζ.autToPow_spec F σ).symm

/-- Every n-th root has the same exponent under the actual absolute Galois
automorphism, for the finite character in
`K2-018#eq:k2018-coefficient-compatibility`. This also treats nonprimitive roots. -/
theorem fromPrimitiveRoot_eval_root (hζ : IsPrimitiveRoot ζ n)
    (σ : Field.absoluteGaloisGroup F) (η : AlgebraicClosure F) (hη : η ^ n = 1) :
    asAutomorphism F σ η = η ^ (fromPrimitiveRoot F hζ σ : ZMod n).val := by
  obtain ⟨j, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [map_pow, fromPrimitiveRoot_eval F hζ σ, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Changing the genuine primitive-root basis does not change the finite
absolute Galois character in `K2-018#eq:k2018-coefficient-compatibility`.
The statement follows from the action on every n-th root; independence is
not part of the constructor's input. -/
theorem fromPrimitiveRoot_independent {η : AlgebraicClosure F}
    (hζ : IsPrimitiveRoot ζ n) (hη : IsPrimitiveRoot η n) :
    fromPrimitiveRoot F hζ = fromPrimitiveRoot F hη := by
  apply MonoidHom.ext
  intro σ
  apply Units.ext
  apply ZMod.val_injective
  apply hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [← fromPrimitiveRoot_eval_root F hζ σ η hη.pow_eq_one,
    ← fromPrimitiveRoot_eval F hη σ]

/-- The residue-class representative of `1` acts as the identity on the
primitive root, even at level one, for
`K2-018#eq:k2018-coefficient-compatibility`. This avoids an assumption `n>1`. -/
theorem primitiveRoot_pow_one (hζ : IsPrimitiveRoot ζ n) :
    ζ ^ (1 : ZMod n).val = ζ := by
  simpa using hζ.autToPow_spec F (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)

/-- The actual cyclotomic character is trivial on an automorphism exactly
when that automorphism fixes the primitive root, for
`K2-018#eq:k2018-coefficient-compatibility`. This is the finite stabilizer
description used to derive continuity. -/
theorem fromPrimitiveRoot_eq_one_iff (hζ : IsPrimitiveRoot ζ n)
    (σ : Field.absoluteGaloisGroup F) :
    fromPrimitiveRoot F hζ σ = 1 ↔ asAutomorphism F σ ζ = ζ := by
  constructor
  · intro hσ
    rw [fromPrimitiveRoot_eval F hζ σ, hσ]
    change ζ ^ (1 : ZMod n).val = ζ
    exact primitiveRoot_pow_one F hζ
  · intro hσ
    apply Units.ext
    apply ZMod.val_injective
    apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    change ζ ^ (fromPrimitiveRoot F hζ σ : ZMod n).val = ζ ^ (1 : ZMod n).val
    rw [← fromPrimitiveRoot_eval F hζ σ, hσ, primitiveRoot_pow_one F hζ]

/-- Continuity of the finite exponent value map is derived from the open
Krull stabilizer of the algebraic primitive root, for
`K2-018#eq:k2018-coefficient-compatibility`. The topology on `ZMod n` is its
actual discrete topology; continuity is not a hypothesis. -/
theorem fromPrimitiveRoot_continuous_value (hζ : IsPrimitiveRoot ζ n) :
    Continuous (fun σ : Field.absoluteGaloisGroup F =>
      (fromPrimitiveRoot F hζ σ : ZMod n)) := by
  let f : (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →* ZMod n :=
    (Units.coeHom (ZMod n)).comp (hζ.autToPow F)
  change Continuous f
  apply continuous_of_continuousAt_one f
  rw [ContinuousAt, map_one, nhds_discrete (ZMod n), tendsto_pure]
  have hopen : IsOpen (MulAction.stabilizer
      (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ζ :
      Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) := stabilizer_isOpen_of_isIntegral ζ
  have hmem : (MulAction.stabilizer (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ζ :
      Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) ∈
        𝓝 (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
    hopen.mem_nhds (Subgroup.one_mem _)
  filter_upwards [hmem] with σ hσ
  have hfix : asAutomorphism F σ ζ = ζ := hσ
  exact congrArg Units.val ((fromPrimitiveRoot_eq_one_iff F hζ σ).mpr hfix)

/-- The finite cyclotomic homomorphism is continuous into the actual unit
group topology, derived from its value map, for
`K2-018#eq:k2018-coefficient-compatibility`. -/
theorem fromPrimitiveRoot_continuous (hζ : IsPrimitiveRoot ζ n) :
    Continuous (fromPrimitiveRoot F hζ) :=
  Continuous.of_coeHom_comp (fromPrimitiveRoot_continuous_value F hζ)

end PrimitiveRoot

section CharacteristicZero

variable (F : Type*) [Field F] [CharZero F] (n : ℕ) [NeZero n]

/-- A primitive root chosen from the proved closed-field existence theorem,
constructing the basis for the actual finite cyclotomic coefficient character
in `K2-018#eq:k2018-coefficient-compatibility`. No root-existence premise is supplied. -/
noncomputable def primitiveRoot : AlgebraicClosure F :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) n).choose

/-- The chosen root is actually primitive, from algebraic closedness and
characteristic zero, for `K2-018#eq:k2018-coefficient-compatibility`. -/
theorem primitiveRoot_spec : IsPrimitiveRoot (primitiveRoot F n) n :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure F) n).choose_spec

/-- The constructed finite cyclotomic homomorphism of the actual absolute
Galois group of a characteristic-zero field, for
`K2-018#eq:k2018-coefficient-compatibility` and the coefficient convention of
`K2-018#prop:k2018-arithmetic-characters`. Its target is the actual unit group. -/
noncomputable def character : Field.absoluteGaloisGroup F →* (ZMod n)ˣ :=
  fromPrimitiveRoot F (primitiveRoot_spec F n)

/-- Root-power characterization on every n-th root in the actual algebraic
closure, for the cyclotomic character in
`K2-018#eq:k2018-coefficient-compatibility`. -/
theorem character_eval (σ : Field.absoluteGaloisGroup F)
    (η : AlgebraicClosure F) (hη : η ^ n = 1) :
    asAutomorphism F σ η = η ^ (character F n σ : ZMod n).val :=
  fromPrimitiveRoot_eval_root F (primitiveRoot_spec F n) σ η hη

/-- The canonical character agrees with the exponent character of every
genuine primitive root, the basis independence for
`K2-018#eq:k2018-coefficient-compatibility`. -/
theorem character_eq_fromPrimitiveRoot {η : AlgebraicClosure F} (hη : IsPrimitiveRoot η n) :
    character F n = fromPrimitiveRoot F hη :=
  fromPrimitiveRoot_independent F (primitiveRoot_spec F n) hη

/-- The finite cyclotomic character's value is a unit, the coefficient
automorphism property used in `K2-018#eq:k2018-coefficient-compatibility`. -/
theorem character_isUnit (σ : Field.absoluteGaloisGroup F) :
    IsUnit (character F n σ : ZMod n) := (character F n σ).isUnit

/-- The actual cyclotomic coefficient character is multiplicative, in the
coefficient convention of `K2-018#eq:k2018-coefficient-compatibility`. -/
theorem character_mul (σ τ : Field.absoluteGaloisGroup F) :
    character F n (σ * τ) = character F n σ * character F n τ :=
  (character F n).map_mul σ τ

/-- Continuity of the actual finite cyclotomic coefficient value, derived
from the Krull topology, for `K2-018#eq:k2018-coefficient-compatibility`. -/
theorem character_continuous_value :
    Continuous (fun σ : Field.absoluteGaloisGroup F => (character F n σ : ZMod n)) :=
  fromPrimitiveRoot_continuous_value F (primitiveRoot_spec F n)

/-- Continuity of the actual finite cyclotomic unit-valued character, for
`K2-018#eq:k2018-coefficient-compatibility`. -/
theorem character_continuous : Continuous (character F n) :=
  fromPrimitiveRoot_continuous F (primitiveRoot_spec F n)

/-- The constructed finite cyclotomic character as a continuous monoid
homomorphism, ready for the finite coefficient interfaces in
`K2-018#prop:k2018-arithmetic-characters`. -/
noncomputable def continuousCharacter : Field.absoluteGaloisGroup F →ₜ* (ZMod n)ˣ :=
  { toMonoidHom := character F n
    continuous_toFun := character_continuous F n }

/-- The scalar unit/additive automorphism interface applied to the actual
constructed character, for the finite coefficient convention in
`K2-018#prop:k2018-arithmetic-characters`. This is the single cyclotomic
weight; no Tate lattice or coefficient scheme is constructed. -/
noncomputable def coefficientAutomorphism (σ : Field.absoluteGaloisGroup F) :
    ZMod n ≃+ ZMod n := AddMonoidHom.CyclicCharacters.unitMarking (character F n σ)

/-- Formula for the actual coefficient automorphism corresponding to the
constructed cyclotomic value, for
`K2-018#prop:k2018-arithmetic-characters`. -/
theorem coefficientAutomorphism_apply (σ : Field.absoluteGaloisGroup F) (a : ZMod n) :
    coefficientAutomorphism F n σ a = (character F n σ : ZMod n) * a := rfl

end CharacteristicZero

end Field.absoluteGaloisGroup.CyclotomicCharacter

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 ea7b905a9872e3fb25f265a02fd51ae8f903d29e2de3a716e1bfba7b18a1ae28.
Definitions, hypotheses and universes are retained modulo native names. -/
