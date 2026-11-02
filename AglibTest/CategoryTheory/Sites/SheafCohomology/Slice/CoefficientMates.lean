/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.CoefficientMates

/-! Public original-map interfaces and approved-axiom guards. -/

@[expose] public section


/-- info: 'CategoryTheory.Sheaf.SliceCohomology.mate_lowerShriekCoefficientIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.SliceCohomology.mate_lowerShriekCoefficientIso
