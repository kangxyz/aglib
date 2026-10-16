/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Flat.UniversalTensor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Flat terms in the original good upper truncation

Universal exactness at the next tensor degree proves that the actual boundary
cycle module is flat. The native good truncation consequently has flat terms:
its interior terms are the original modules, its boundary is the original
cycles, and its terms above the bound are zero. The complex and inclusion are
the unchanged native truncation objects and maps.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- The native good upper truncation has flat terms when the original terms
are flat and the following middle tensor degree is universally exact. -/
theorem flat_truncLE_X_of_universally_lTensor_exact
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ)
    [∀ i, Module.Flat R (K.X i)]
    (h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Exact ((K.d b (b + 1)).hom.lTensor N)
        ((K.d (b + 1) (b + 2)).hom.lTensor N)) (q : ℤ) :
    Module.Flat R ((K.truncLE b).X q) := by
  obtain hq | hq | hq := lt_trichotomy q b
  · exact Module.Flat.of_linearEquiv (K.truncLEXIso b q hq).toLinearEquiv
  · subst q
    let := K.flat_cycles_of_universally_lTensor_exact b h
    exact Module.Flat.of_linearEquiv (K.truncLEXIsoCycles b).toLinearEquiv
  · let := ModuleCat.subsingleton_of_isZero ((K.truncLE b).isZero_of_isStrictlyLE b q hq)
    infer_instance

end CochainComplex
