/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Basic
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian
/-!
# Finite presentations of affine coherent sheaves

A finite module over a noetherian ring has finitely many generators and
relations. Applying the actual tilde functor gives a finite presentation of
its sheaf. Consequently every object of the affine coherent category is a
finitely presented sheaf in the existing sheaf-theoretic sense.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Affine coherent sheaves satisfy the local finite-presentation predicate;
this is a proved comparison, rather than a renaming of unrelated categories. -/
theorem affineCoherent_finitePresentation (M : AffineFiniteType R) :
    ((affineFiniteTypeToModules R).obj M).IsFinitePresentation := by
  let N := (affineFiniteTypeToModules R).obj M
  have : N.IsQuasicoherent := M.obj.property
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  exact (SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf).prop_of_iso
    (asIso N.fromTildeΓ) (finitePresentation_tilde R (moduleSpecΓFunctor.obj N))

/-- The inclusion of affine coherent sheaves into the actual full subcategory
of finitely presented sheaves. -/
def affineCoherentToFinitePresentation :
    AffineFiniteType R ⥤ Scheme.Modules.FinitePresentation (Spec R) :=
  (Scheme.Modules.finitePresentation (Spec R)).lift (affineFiniteTypeToModules R)
    (affineCoherent_finitePresentation R)

end AlgebraicGeometry.Scheme.Modules.Coherent
