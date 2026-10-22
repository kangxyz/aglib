/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoverSystem
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.IntersectionComparison
public import Aglib.AlgebraicGeometry.Spec.ResidueFiber

/-!
# The native first stage and the literal residue fibre

These comparisons retain the original inclusion into the ambient scheme. The
prescribed input cover lives on the actual categorical residue pullback, and
only its native first-stage transport is used to construct the nilpotent tower.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A))

/-- The canonical original native first-stage comparison with the actual residue fibre. -/
def residueStageIso :
    (Modules.idealThickeningIdealSheaf f (IsLocalRing.maximalIdeal A) ^ 1).subscheme ≅
      pullback f (LocalRing.residueSpecMap A) :=
  IdealSheafData.subschemeIsoOfEq (pow_one _) ≪≫
    Modules.idealThickeningSubschemeIso f (IsLocalRing.maximalIdeal A)

@[reassoc (attr := simp)]
theorem residueStageIso_hom_fst :
    (residueStageIso f).hom ≫ pullback.fst f (LocalRing.residueSpecMap A) =
      (Modules.idealThickeningIdealSheaf f (IsLocalRing.maximalIdeal A) ^ 1).subschemeι := by
  simp only [residueStageIso, Iso.trans_hom, Category.assoc]
  rw [show pullback.fst f (LocalRing.residueSpecMap A) =
    Modules.idealThickeningι f (IsLocalRing.maximalIdeal A) from rfl]
  simp

/-- The genuine tower supplier starts with a cover of the literal residue fibre. -/
def residueCoverSystem (C : FiniteEtale (pullback f (LocalRing.residueSpecMap A))) :
    CoverSystem (Modules.idealThickeningIdealSheaf f (IsLocalRing.maximalIdeal A)) :=
  coverSystem _ ((baseChange (residueStageIso f).hom).obj C)

@[simp]
theorem residueCoverSystem_cover_one
    (C : FiniteEtale (pullback f (LocalRing.residueSpecMap A))) :
    (residueCoverSystem f C).cover 1 = (baseChange (residueStageIso f).hom).obj C := rfl

/-- Restricting a global cover to the native first stage is the literal residue
restriction followed by its original scheme comparison. -/
def residueStageBaseChangeIso :
    baseChange (pullback.fst f (LocalRing.residueSpecMap A)) ⋙
      baseChange (residueStageIso f).hom ≅
    baseChange (Modules.idealThickeningIdealSheaf f (IsLocalRing.maximalIdeal A) ^ 1).subschemeι :=
  (baseChangeComp (pullback.fst f (LocalRing.residueSpecMap A))
    (residueStageIso f).hom).symm ≪≫
      eqToIso (congrArg baseChange (residueStageIso_hom_fst f))

/-- Transport the specified native first-stage isomorphism back to the original
residue-fibre pullback functor. No replacement public fibre is introduced. -/
def literalResidueCoverIso (Y : FiniteEtale X)
    (C : FiniteEtale (pullback f (LocalRing.residueSpecMap A)))
    (e : (baseChange
      (Modules.idealThickeningIdealSheaf f (IsLocalRing.maximalIdeal A) ^ 1).subschemeι).obj Y ≅
        (residueCoverSystem f C).cover 1) :
    (baseChange (pullback.fst f (LocalRing.residueSpecMap A))).obj Y ≅ C := by
  let F := baseChange (residueStageIso f).hom
  letI : F.Full := baseChange_full_of_isIso _
  letI : F.Faithful := baseChange_faithful_of_isIso _
  exact F.preimageIso ((residueStageBaseChangeIso f).app Y ≪≫ e)

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
