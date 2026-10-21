/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.Kummer.Basic
public import Aglib.RingTheory.RootsOfUnity.BaseField

/-!
# Galois action on roots of base-field units

For every field and every natural level, the actual unit action fixes the image of a base-field
root of unity. The nth power of any root of a base-field unit is fixed as well. These
statements use the existing roots, coefficient inclusion and unit action, including level zero.

Extraction source: `R5Lab.Aglib.GroupCohomology.Kummer.RootAction`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3cbce6edfa4dbba1bf005acf3537fd9d6b6ee425a0996f8e951a4772c9c68b32`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

noncomputable section
namespace GroupCohomology.Kummer

open Field.absoluteGaloisGroup.RootsOfUnity
universe u
variable {K : Type u} [Field K]
variable (K) (n : ℕ)

/-- The canonical image of a base-field root is fixed by the actual unit action. -/
theorem unitAction_baseRoot (z : rootsOfUnity n K) (g : Field.absoluteGaloisGroup K) :
    Kummer.unitAction K g ((baseRoot K n z).toMul : (AlgebraicClosure K)ˣ) =
      ((baseRoot K n z).toMul : (AlgebraicClosure K)ˣ) := by
  exact congrArg (fun x : Mu K n => (x.toMul : (AlgebraicClosure K)ˣ))
    (baseRoot_fixed K n z g)

/-- The nth power of a root of a base-field unit is fixed by the actual unit action. -/
theorem unitAction_pow_eq (a : Kˣ) (b : (AlgebraicClosure K)ˣ)
    (hb : b ^ n = Kummer.baseUnits K a) (g : Field.absoluteGaloisGroup K) :
    (Kummer.unitAction K g b)^n = b ^ n := by
  calc
    (Kummer.unitAction K g b)^n = Kummer.baseUnits K a := by
      rw [← map_pow, hb, Kummer.unitAction_base]
    _ = b ^ n := hb.symm

end GroupCohomology.Kummer
