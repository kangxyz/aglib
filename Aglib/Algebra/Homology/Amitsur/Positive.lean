/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Exactness

/-!
# Acyclicity and positive Amitsur cohomology

The original augmented complex is acyclic. Removing its original augmentation
leaves the original unaugmented Amitsur complex, whose positive homology objects
therefore vanish. Neither claim imposes a flatness condition on the coefficient module.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Amitsur

universe u v

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [Module.FaithfullyFlat R S] (M : ModuleCat.{max u v} R)

/-- The actual augmented Amitsur complex of the original module is acyclic. -/
theorem augmentedComplex_acyclic : (augmentedComplex R S M).Acyclic :=
  augmentedComplex_exactAt R S M

/-- The original unaugmented Amitsur complex is exact in every positive degree. -/
theorem complex_exactAt_succ (n : ℕ) : (complex R S M).ExactAt (n + 1) := by
  have h := ((augmentedComplex R S M).exactAt_iff' (n + 1) (n + 2) (n + 3)
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) by rfl))
    ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (n + 2) (n + 3) by rfl))).mp
      (augmentedComplex_exactAt R S M (n + 2))
  apply ((complex R S M).exactAt_iff' n (n + 1) (n + 2)
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) by rfl))
    ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) by rfl))).mpr
  change ((complex R S M).sc' n (n + 1) (n + 2)).Exact at h
  exact h

/-- Every positive homology object of the original unaugmented complex vanishes. -/
theorem isZero_homology_complex_succ (n : ℕ) :
    IsZero ((complex R S M).homology (n + 1)) :=
  (complex_exactAt_succ R S M n).isZero_homology

end ModuleCat.Amitsur
