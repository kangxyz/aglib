/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.AmpleCriterion

/-!
# Effective finite-kernel ampleness on the same original group and Picard representative

Both actual scheme-kernel formulations retain nilpotent structure. No smoothness,
properness, dimension, or reducedness of the dual component is an input.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G]
  [IsHProjective G.hom] [GeometricallyIntegral G.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example (L : LineBundle G.left) (s : Γ(L.val, ⊤)) (hs : s ≠ 0)
    (hK : IsFinite (Group.Kernel.group
      (lineBundleClassGroupHom G P R (classOf G.left L))).X.hom) : L.IsAmple :=
  isAmple_of_section_ne_zero_of_finite_kernel G P R L s hs hK

example (L : LineBundle G.left) (hs : ∃ s : Γ(L.val, ⊤), s ≠ 0)
    (hK : IsFinite (Group.Kernel.group
      (lineBundleClassIdentityComponentGroupHom G P R (classOf G.left L))).X.hom) :
    L.IsAmple := by
  obtain ⟨s, hs⟩ := hs
  exact isAmple_of_section_ne_zero_of_finite_identityComponent_kernel G P R L s hs hK

end

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isAmple_of_section_ne_zero_of_finite_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isAmple_of_section_ne_zero_of_finite_kernel

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isAmple_of_section_ne_zero_of_finite_identityComponent_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isAmple_of_section_ne_zero_of_finite_identityComponent_kernel
