/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.InternalExtComparison

/-! # Native local-Ext supplier tests and standard axiom guards -/

/-- info: 'CategoryTheory.Sheaf.InternalExt.homFunctor_injective_ext_subsingleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.homFunctor_injective_ext_subsingleton

/-- info: 'CategoryTheory.Sheaf.InternalExt.moduleExtAddEquivOfAcyclic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.moduleExtAddEquivOfAcyclic

/-- info: 'CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic

/-- info: 'CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic_apply

/-- info: 'CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic_mk₀' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic_mk₀

/-- info: 'CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic_zero

/-- info: 'CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic_naturality


/-- info: 'CategoryTheory.Sheaf.InternalExt.moduleExtReverse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.moduleExtReverse

/-- info: 'CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse

/-- info: 'CategoryTheory.Sheaf.InternalExt.moduleExtReverse_eq_symm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.moduleExtReverse_eq_symm

/-- info: 'CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_eq_symm' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_eq_symm




/-- info: 'CategoryTheory.Sheaf.InternalExt.cohomologyExtReverseAfterComparison' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.cohomologyExtReverseAfterComparison



/-- info: 'CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_zero_of_acyclic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_zero_of_acyclic

/-- info: 'CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_naturality_of_acyclic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Sheaf.InternalExt.cohomologyExtReverse_naturality_of_acyclic
