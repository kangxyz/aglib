/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.FiniteCharacter
public import Mathlib.Data.ZMod.Basic

/-!
# Compatibility of finite cyclotomic characters

Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.CharacterCompatibility`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

namespace Field.absoluteGaloisGroup.CyclotomicCharacter
variable (F : Type*) [Field F] [CharZero F]

section DivisorLevel

variable {d n : ℕ} [NeZero d] [NeZero n]

/-- The actual divisor-level root in the common algebraic closure, for the
cyclotomic coefficient convention of `K2-018#eq:k2018-coefficient-compatibility`.
It is obtained by powering the chosen n-th root, not by supplying a character. -/
noncomputable def divisorPrimitiveRoot (_h : d ∣ n) : AlgebraicClosure F :=
  _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot F n ^ (n / d)

omit [NeZero d] in
/-- Powering the genuine primitive n-th root by `n / d` gives a primitive
d-th root, the root comparison underlying
`K2-018#eq:k2018-coefficient-compatibility`. -/
theorem divisorPrimitiveRoot_spec (h : d ∣ n) :
    IsPrimitiveRoot (divisorPrimitiveRoot F h) d :=
  IsPrimitiveRoot.pow (NeZero.pos n)
    (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.primitiveRoot_spec F n)
    (Nat.div_mul_cancel h).symm

omit [NeZero d] in
/-- The actual ring reduction sends residue-class representatives to their
mod-d representatives, the coefficient arithmetic used in
`K2-018#eq:k2018-coefficient-compatibility`. -/
theorem reduction_val (h : d ∣ n) (a : ZMod n) :
    ((ZMod.castHom h (ZMod d)) a).val = a.val % d := by
  calc
    ((ZMod.castHom h (ZMod d)) a).val =
        ((ZMod.castHom h (ZMod d)) (a.val : ZMod n)).val :=
      congrArg (fun x : ZMod n => ((ZMod.castHom h (ZMod d)) x).val)
        (ZMod.natCast_zmod_val a).symm
    _ = (a.val : ZMod d).val := by rw [map_natCast]
    _ = a.val % d := ZMod.val_natCast d a.val

omit [CharZero F] [NeZero d] in
/-- Reducing an exponent does not change its action on a primitive d-th
root, the root-exponent comparison for
`K2-018#eq:k2018-coefficient-compatibility`. The root itself is actual field data. -/
theorem primitiveRoot_pow_reduction (h : d ∣ n) {η : AlgebraicClosure F}
    (hη : IsPrimitiveRoot η d) (a : ZMod n) :
    η ^ ((ZMod.castHom h (ZMod d)) a).val = η ^ a.val := by
  rw [reduction_val]
  simpa only [← hη.eq_orderOf] using pow_mod_orderOf η a.val

/-- Actual cross-level compatibility of the constructed cyclotomic
characters for `K2-018#eq:k2018-coefficient-compatibility`. Comparison uses
the primitive divisor-level root in the same algebraic closure; no `hchi`
or abstract compatibility record is supplied. -/
theorem character_reduction (h : d ∣ n) (σ : Field.absoluteGaloisGroup F) :
    (ZMod.castHom h (ZMod d)) (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character F
      n σ : ZMod n) =
      (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character F d σ : ZMod d) := by
  let η := divisorPrimitiveRoot F h
  have hη : IsPrimitiveRoot η d := divisorPrimitiveRoot_spec F h
  have hηn : η ^ n = 1 := (hη.pow_eq_one_iff_dvd n).mpr h
  have hn := _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character_eval F n σ η hηn
  have hd := _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character_eval F d σ η
    hη.pow_eq_one
  apply ZMod.val_injective
  apply hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  calc
    η ^ ((ZMod.castHom h (ZMod d))
        (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character F n σ : ZMod n)).val =
        η ^ (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character F n σ : ZMod n).val :=
      primitiveRoot_pow_reduction F h hη _
    _ = _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.asAutomorphism F σ η := hn.symm
    _ = η ^ (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character F d σ : ZMod d).val
      := hd

/-- Cross-level compatibility in the actual coefficient unit groups, for
`K2-018#eq:k2018-coefficient-compatibility`. This strengthens the value-map
formula to equality of cyclotomic units. -/
theorem character_reduction_units (h : d ∣ n) (σ : Field.absoluteGaloisGroup F) :
    Units.map ((ZMod.castHom h (ZMod d))).toMonoidHom
      (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character F n σ) =
        _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character F d σ := by
  apply Units.ext
  exact character_reduction F h σ

/-- Compatibility as an equality of actual cyclotomic homomorphisms, for
`K2-018#eq:k2018-coefficient-compatibility`. -/
theorem character_reduction_hom (h : d ∣ n) :
    (Units.map ((ZMod.castHom h (ZMod d))).toMonoidHom).comp
      (_root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character F n) =
        _root_.Field.absoluteGaloisGroup.CyclotomicCharacter.character F d :=
  MonoidHom.ext (character_reduction_units F h)

end DivisorLevel

end Field.absoluteGaloisGroup.CyclotomicCharacter
