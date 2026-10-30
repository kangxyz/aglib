/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.AmpleKernel

/-!
# Original Picard and identity-component kernels of an ample line bundle

The consumer retains one supplied Picard representative and needs no dual
smoothness, dimension, properness, reducedness or prime-to-characteristic premise.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AglibTest.AbelianVarietyLineBundleKernel

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G]
  [IsProper G.hom] [Flat G.hom] [GeometricallyIntegral G.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf G.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example (L : LineBundle G.left) (hL : L.IsAmple) :
    IsFinite (Group.Kernel.group (lineBundleClassGroupHom G P R (classOf G.left L))).X.hom :=
  isFinite_kernel_lineBundleClassGroupHom G P R L hL

example (L : LineBundle G.left) (hL : L.IsAmple) :
    IsFinite (Group.Kernel.group
      (lineBundleClassIdentityComponentGroupHom G P R (classOf G.left L))).X.hom :=
  isFinite_kernel_lineBundleClassIdentityComponentGroupHom G P R L hL

end AglibTest.AbelianVarietyLineBundleKernel

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isFinite_kernel_lineBundleClassGroupHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isFinite_kernel_lineBundleClassGroupHom

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isFinite_kernel_lineBundleClassIdentityComponentGroupHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isFinite_kernel_lineBundleClassIdentityComponentGroupHom
