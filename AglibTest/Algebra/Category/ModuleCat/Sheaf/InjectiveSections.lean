/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InjectiveSections

/-! # Original section-supplier axiom guards -/

/-- info: 'ModuleCat.Sheaf.sections_preservesInjectiveObjects' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.sections_preservesInjectiveObjects

/-- info: 'ModuleCat.Sheaf.moduleInjective_sections' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.moduleInjective_sections
