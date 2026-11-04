/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FramePushout

/-! # Cohomology classes of the original family frame and coframe comparisons -/

@[expose] public section

open CategoryTheory CategoryTheory.MonObj AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open Scheme.OverField Scheme.EtaleCohomology
open Scheme.Modules.Invertible Scheme.Modules.Invertible.FrameInverse
open GroupCohomology.Kummer.Coefficients

universe u w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
  familyCoefficient_isCommMonObj

variable {k : Type u} [Field k] {A B : Grp (FScheme k)} (q : A ⟶ B)
  (T : FScheme k) [IsCommMonObj A.X]
  [IsFinite q.hom.hom.left] [Etale q.hom.hom.left] [Surjective q.hom.hom.left]
  [IsProper A.X.hom] [GeometricallyIntegral A.X.hom]

set_option hygiene false in
local notation "Aₜ" => Functor.obj (Functor.mapGrp (Over.pullback T.hom)) A
set_option hygiene false in
local notation "Bₜ" => Functor.obj (Functor.mapGrp (Over.pullback T.hom)) B

variable (M : LineBundle (Bₜ).X.left)
  (a : (Modules.pullback (familyMapOfHom q.hom.hom T)).obj M.val ≅
    SheafOfModules.unit (Aₜ).X.left.ringCatSheaf)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} (Bₜ).X.left)]

/-- Pushing the original cover class along the positive family character gives
the Picard class under the original frame equivalence. -/
theorem familyFrameClass_eq :
    coefficientMap (representedSheafMap (familyCharacter q T M a))
        (torsorExtClass (familyCoverTorsor q T)) =
      FrameTensor.picardH1Equiv.{u, w} (Bₜ).X.left (classOf (Bₜ).X.left M) :=
  (torsorExtClass_naturality (familyFrameHom q T M a)).trans
    (FrameTensor.picardH1Equiv_classOf (Bₜ).X.left M).symm

/-- Pushing the same cover class along the inverse character gives the negative
Picard class, represented by the original coframe torsor. -/
theorem familyCoframeClass_eq :
    coefficientMap (representedSheafMap (familyCharacter q T M a) ≫ (-𝟙 (gm (Bₜ).X.left)))
        (torsorExtClass (familyCoverTorsor q T)) =
      FrameTensor.picardH1Equiv.{u, w} (Bₜ).X.left (-classOf (Bₜ).X.left M) :=
  (torsorExtClass_naturality (familyCoframeHom q T M a)).trans
    (torsorExtClass_coframe_picard (Bₜ).X.left M)

end AlgebraicGeometry.Scheme.RelativePicard.KernelFramePushout
