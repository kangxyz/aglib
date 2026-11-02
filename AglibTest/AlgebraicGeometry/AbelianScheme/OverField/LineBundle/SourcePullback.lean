/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.SourcePullback

/-! # Original source-hom law for the line-bundle morphism -/

@[expose] public section

open AlgebraicGeometry.Scheme.RelativePicard

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.translationFamilyClass_sourceHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms translationFamilyClass_sourceHom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.lineBundleClassMorphism_sourceHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lineBundleClassMorphism_sourceHom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.lineBundleClassMorphismIdentityComponent_sourceHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms lineBundleClassMorphismIdentityComponent_sourceHom
