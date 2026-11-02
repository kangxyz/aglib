/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.InternalHomSource

/-! # Original source internal-Hom maps and exactness axiom guards -/

/-- info: 'ModuleCat.Sheaf.ConstantRing.sourceFunctor_preservesHomology_of_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.sourceFunctor_preservesHomology_of_injective

/-- info: 'ModuleCat.Sheaf.ConstantRing.shortExact_source_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.shortExact_source_injective

/-- info: 'ModuleCat.Sheaf.ConstantRing.shortExact_sourceComplex_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ModuleCat.Sheaf.ConstantRing.shortExact_sourceComplex_injective
