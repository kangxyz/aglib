/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.NormalizedChart

/-! Axiom guard for the original normalized chart value. -/

open AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardRepresenterNormalizedEtaleIso_hom_app_of_family'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms picardRepresenterNormalizedEtaleIso_hom_app_of_family
