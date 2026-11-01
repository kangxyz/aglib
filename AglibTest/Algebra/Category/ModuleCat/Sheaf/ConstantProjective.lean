/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantProjective

/-! # Original local-boundary supplier axiom guards -/

/-- info: 'ModuleCat.Presheaf.exists_cover_projective_lift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Presheaf.exists_cover_projective_lift

/-- info: 'ModuleCat.Sheaf.exists_cover_constant_projective_lift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.exists_cover_constant_projective_lift

/-- info: 'ModuleCat.Sheaf.exists_cover_projective_boundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.exists_cover_projective_boundary

/-- info: 'ModuleCat.Sheaf.exists_cover_projective_boundary_of_exactAt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.exists_cover_projective_boundary_of_exactAt
