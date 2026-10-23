/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Comparison

/-!
# Faithfully flat exactness of the original augmented Amitsur complex

The actual scalar-extended original complex contracts by multiplication
of its leading scalar factors. Native faithfully flat exactness reflection
then proves exactness of the original complex in every degree, for any
original coefficient module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Amitsur

universe u v

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S] (M : ModuleCat.{max u v} R)

/-- The actual augmented Amitsur complex of an arbitrary module is exact
in every degree under faithfully flat scalar extension. -/
theorem augmentedComplex_exactAt (n : ℕ) : (augmentedComplex R S M).ExactAt n :=
  (exactAt_iff_scalarTensor R S (augmentedComplex R S M) n).mp
    (scalarTensor_augmentedComplex_exactAt R S M n)

/-- Every actual homology object of the original augmented Amitsur complex vanishes. -/
theorem isZero_homology_augmentedComplex (n : ℕ) :
    IsZero ((augmentedComplex R S M).homology n) :=
  (augmentedComplex_exactAt R S M n).isZero_homology

end ModuleCat.Amitsur
