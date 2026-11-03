/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# The original generic point in a spectrum of a stalk

For an integral scheme, its actual local-spectrum map sends the zero prime
to the original generic point. No closed immersion, Noetherianity or
dimension condition is used.

The implementation is moved unchanged from the former private helper in
`Morphisms/ClosedImmersion/ComponentStalk.lean`, at HEAD 4447b30a.
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

end AlgebraicGeometry.Scheme
