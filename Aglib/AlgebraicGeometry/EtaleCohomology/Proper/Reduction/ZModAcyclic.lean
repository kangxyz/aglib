/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModImages
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.HigherImageAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic

/-! # Relative acyclicity of the original underlying injective module

The published genuine-module/ringed-module equivalence and its original
underlying comparison transport the native represented-object Ext vanishing.
The actual direct image is therefore acyclic on these original underlying
coefficients. This uses no injectivity claim after scalar forgetting.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

universe u e

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  TorsionZMod.Ringed.hasSheafifyRingStandard TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

/-- Every original free representable has vanishing positive Ext into the
original underlying coefficient of a genuine injective ZMod-module sheaf. -/
theorem zmodInjective_representedExt_subsingleton
    (X : Scheme.{u}) [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (n : ℕ) (I : ZModSheaf X n) [Injective I] (U : X.Etale) (q : ℕ) :
    Subsingleton (Ext.{e} (freeAbelianSheaf.{u + 1} X.smallEtaleTopology U)
      ((zmodUnderlying X n).obj I) (q + 1)) := by
  let J := X.smallEtaleTopology
  let R : Sheaf J RingCat.{u + 1} :=
    TorsionZMod.Ringed.constantRingSheaf.{u + 1, u, u + 1} J n
  let E : ZModSheaf X n ≌ SheafOfModules.{u + 1} R :=
    TorsionZMod.Ringed.equivalenceStandard.{u + 1, u} J n
  let η : E.functor ⋙ SheafOfModules.toSheaf R ≅ zmodUnderlying X n :=
    TorsionZMod.Ringed.forwardUnderlyingIsoStandard.{u + 1, u} J n
  have : Injective (E.functor.obj I) :=
    E.functor.injective_obj_of_injective (inferInstance : Injective I)
  have hM : Subsingleton
      (Ext.{e} (freeAbelianSheaf.{u + 1} J U)
        ((SheafOfModules.toSheaf R).obj (E.functor.obj I)) (q + 1)) :=
    Sheaf.ModuleCoefficients.toSheaf_injective_ext_subsingleton_largeScalars
      R (E.functor.obj I) U q
  exact TorsionZMod.subsingleton_of_additiveIso
    ((extFunctorObj (freeAbelianSheaf.{u + 1} J U) (q + 1)).mapIso (η.app I)) hM

/-- A genuine injective ZMod-module sheaf has acyclic original underlying
coefficients for the actual direct image along every scheme morphism. -/
theorem higherDirectImage_zmodInjective_isZero
    {X S : Scheme.{u}} [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (f : X ⟶ S) (n : ℕ) (I : ZModSheaf X n) [Injective I] (q : ℕ) :
    IsZero ((higherDirectImage f (q + 1)).obj ((zmodUnderlying X n).obj I)) :=
  higherDirectImage_isZero_of_representedExt_vanishing f ((zmodUnderlying X n).obj I)
    (fun U k => zmodInjective_representedExt_subsingleton X n I U k) q

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
