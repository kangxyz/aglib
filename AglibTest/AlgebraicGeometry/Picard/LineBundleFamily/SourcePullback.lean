/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LineBundleFamily.SourcePullback

/-! # Whole nonflat source pullback and difference-family laws -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.pullbackClass_familyMapOfHom_translationFamilyClass_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.pullbackClass_familyMapOfHom_translationFamilyClass_naturality

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.pullbackClass_familyMapOfHom_translationFamilyClass_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.pullbackClass_familyMapOfHom_translationFamilyClass_inv
