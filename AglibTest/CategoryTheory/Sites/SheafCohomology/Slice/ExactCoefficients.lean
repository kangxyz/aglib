/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.ExactCoefficients

/-! # Original generic slice-exactness axiom guards -/

/-- info: 'CategoryTheory.GrothendieckTopology.overPullback_additive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.overPullback_additive

/-- info: 'CategoryTheory.GrothendieckTopology.overPullback_preservesLimitsOfShape' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.overPullback_preservesLimitsOfShape

/-- info: 'CategoryTheory.GrothendieckTopology.overPullback_preservesFiniteLimits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.overPullback_preservesFiniteLimits

/-- info: 'CategoryTheory.GrothendieckTopology.overPullback_preservesEpimorphisms' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.overPullback_preservesEpimorphisms

/-- info: 'CategoryTheory.GrothendieckTopology.overPullback_preservesHomology' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.overPullback_preservesHomology

/-- info: 'CategoryTheory.GrothendieckTopology.overPullback_preservesFiniteColimits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.overPullback_preservesFiniteColimits

/-- info: 'CategoryTheory.GrothendieckTopology.overPullback_map_isLocallySurjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.overPullback_map_isLocallySurjective
