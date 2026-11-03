/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Tactic.NormNum

/-!
# Original generic points and dimensions of actual stalks

For an integral scheme, its actual local-spectrum map sends the zero prime
to the original generic point. No closed immersion, Noetherianity or
dimension condition is used.
An actual stalk of dimension two is not the generic field stalk; this
companion requires only integrality and that original dimension equality.

The implementation is moved unchanged from the former private helper in
`Morphisms/ClosedImmersion/ComponentStalk.lean`, at HEAD 4447b30a.
The public dimension-two theorem is moved unchanged from
`Surfaces/Birational/Factorization.lean`, retaining its original name.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The zero prime in the actual integral stalk maps to the original
generic point under the original local-spectrum map. -/
lemma fromSpecStalk_bot {C : Scheme.{u}} [IsIntegral C] (c : C) :
    C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c)) = genericPoint C := by
  have hgB : IsGenericPoint (⊥ : PrimeSpectrum (C.presheaf.stalk c)) Set.univ := by
    rw [IsGenericPoint, PrimeSpectrum.closure_singleton]
    simp
  have hd : DenseRange (C.fromSpecStalk c) := by
    rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
    rw [← (genericPoint_spec C).def]
    apply closure_mono
    apply Set.singleton_subset_iff.mpr
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec C).specializes trivial
  have hg : IsGenericPoint
      (C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c))) Set.univ := by
    change closure {C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c))} = Set.univ
    calc
      closure {C.fromSpecStalk c (⊥ : PrimeSpectrum (C.presheaf.stalk c))} =
          closure ((C.fromSpecStalk c) '' Set.univ) :=
        (hgB.image (C.fromSpecStalk c).continuous).def
      _ = closure (Set.range (C.fromSpecStalk c)) := by rw [Set.image_univ]
      _ = Set.univ := hd.closure_range
  exact hg.eq (genericPoint_spec C)

/-- An original stalk of dimension two cannot be the integral scheme's generic field stalk. -/
theorem ne_genericPoint_of_stalk_dimension_two {X : Scheme.{u}} [IsIntegral X]
    (x : X) (hd : ringKrullDim (X.presheaf.stalk x) = 2) : x ≠ genericPoint X := by
  intro h
  subst x
  change ringKrullDim X.functionField = 2 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

end AlgebraicGeometry.Scheme
