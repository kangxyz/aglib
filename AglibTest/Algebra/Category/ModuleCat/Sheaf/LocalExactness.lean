/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.LocalExactness

/-! # Original local-boundary supplier axiom guards -/

/-- info: 'SheafOfModules.exact_of_local_boundaries' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.exact_of_local_boundaries

/-- info: 'SheafOfModules.exactAt_of_local_boundaries' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SheafOfModules.exactAt_of_local_boundaries
