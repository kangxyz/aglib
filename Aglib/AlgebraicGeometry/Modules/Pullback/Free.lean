/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
/-! # Original pullback comparisons for free module sheaves

The structure module, free module sheaves and restriction comparisons are constructed
using the original geometric pullback adjunction and composition isomorphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}}

/-- Pullback carries the structure sheaf, viewed as its unit module, to the
structure sheaf on the source. -/
def pullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
by
  have : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  exact asIso (C := SheafOfModules.{u} X.ringCatSheaf)
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

/-- The canonical pullback isomorphism for a free module sheaf retains its
actual generator type. -/
def pullbackFreeIso (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

/-- Restriction of an actual pullback to an inverse-image open is the pullback
of the restricted module along the restricted scheme morphism. -/
def pullbackRestrictIso (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm _

end AlgebraicGeometry.Scheme.Modules
