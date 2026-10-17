/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Resolution
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Transporting an actual derived global-sections model to an affine-base direct image

The original spectrum-section comparison identifies sections of the actual
pushed injective resolution with the original structural-ring sections.
Exact tilde transports an actual native derived-object comparison using its
installed derived units. The final arrow is the original tilde/sections
counit on that same pushed resolution. Its quasi-isomorphism is proved for
qcqs morphisms and quasicoherent coefficients by the existing supplier.

No new chain representative is selected. Comparison with a separately
chosen chain-normalized model remains a further normalization statement.
The construction imposes no finite-projective or Noetherian hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  {M : X.Modules} (I : InjectiveResolution M)

/-- The standard derived-category structure on the indicated module category. -/
local instance derivedModelSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on the indicated module category. -/
local instance derivedModelModules : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on the indicated module category. -/
local instance derivedModelTarget : HasDerivedCategory.{u + 1} (Spec R).Modules :=
  HasDerivedCategory.standard _

local instance derivedModelTildeUnit : IsIso (tilde.functor R).rightDerivedFunctorPlusUnit :=
  (tilde.functor R).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology

/-- The native bounded-below packing of the original spectrum-section comparison on the
actual pushed injective resolution. -/
def moduleResolutionPushforwardSectionsPlusIso :
    moduleSpecΓFunctor.mapCochainComplexPlus.obj
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus) ≅
      (moduleGlobalSectionsFunctorOfHom X
        (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)).mapCochainComplexPlus.obj
          I.cochainComplexPlus :=
  (CochainComplex.plus (ModuleCat.{u} R)).isoMk
    (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex)

/-- The underlying arrow is the original actual section-complex isomorphism. -/
theorem moduleResolutionPushforwardSectionsPlusIso_hom :
    (moduleResolutionPushforwardSectionsPlusIso f I).hom.hom =
      (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex).hom := rfl

/-- The original affine tilde/global-sections counit on the same pushed resolution, with
its actual bounded-below packing. -/
def moduleResolutionPushforwardTildeCounitPlus :
    (tilde.functor R).mapCochainComplexPlus.obj
        (moduleSpecΓFunctor.mapCochainComplexPlus.obj
          ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus)) ⟶
      (Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus :=
  ⟨Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ)
    (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj)⟩

/-- The packed counit retains the literal original chain arrow. -/
theorem moduleResolutionPushforwardTildeCounitPlus_hom :
    (moduleResolutionPushforwardTildeCounitPlus f I).hom =
      Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ)
        (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj) :=
  rfl

variable (P : CochainComplex.Plus (ModuleCat.{u} R))
  (e : DerivedCategory.Plus.Q.obj P ≅
    (moduleGlobalSectionsFunctorOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))

/-- An actual derived global-sections model identifies with the spectrum sections of the
same original pushed resolution through its original injective-resolution comparison. -/
def moduleSpecDerivedModelSectionsIso :
    DerivedCategory.Plus.Q.obj P ≅
      DerivedCategory.Plus.Q.obj (moduleSpecΓFunctor.mapCochainComplexPlus.obj
        ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus)) :=
  e ≪≫ (I.rightDerivedFunctorPlusIso (moduleGlobalSectionsFunctorOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom))).symm ≪≫
    DerivedCategory.Plus.Q.mapIso (moduleResolutionPushforwardSectionsPlusIso f I).symm

/-- Exact tilde transports the actual model by its original derived units, followed by
the original counit on the same pushed resolution and its original derived comparison. -/
def moduleSpecDerivedPushforwardModelIsoOfCounit
    (hcounit : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ)
      (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj))) :
    DerivedCategory.Plus.Q.obj ((tilde.functor R).mapCochainComplexPlus.obj P) ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) := by
  let S := moduleSpecΓFunctor.mapCochainComplexPlus.obj
    ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus)
  let : IsIso (DerivedCategory.Plus.Q.map (moduleResolutionPushforwardTildeCounitPlus f I)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso (Spec R).Modules) _ hcounit
  exact asIso ((tilde.functor R).rightDerivedFunctorPlusUnit.app P) ≪≫
    (tilde.functor R).rightDerivedFunctorPlus.mapIso (moduleSpecDerivedModelSectionsIso f I P e) ≪≫
    (asIso ((tilde.functor R).rightDerivedFunctorPlusUnit.app S)).symm ≪≫
    asIso (DerivedCategory.Plus.Q.map (moduleResolutionPushforwardTildeCounitPlus f I)) ≪≫
    I.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward f)

/-- The forward comparison retains the two exact-tilde derived units, the actual section
comparison, the literal original counit and the installed resolution comparison. -/
theorem moduleSpecDerivedPushforwardModelIsoOfCounit_hom
    (hcounit : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ)
      (((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus).obj))) :
    (moduleSpecDerivedPushforwardModelIsoOfCounit f I P e hcounit).hom =
      (tilde.functor R).rightDerivedFunctorPlusUnit.app P ≫
        (tilde.functor R).rightDerivedFunctorPlus.map
          (moduleSpecDerivedModelSectionsIso f I P e).hom ≫
        inv ((tilde.functor R).rightDerivedFunctorPlusUnit.app
          (moduleSpecΓFunctor.mapCochainComplexPlus.obj
            ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus))) ≫
        DerivedCategory.Plus.Q.map (moduleResolutionPushforwardTildeCounitPlus f I) ≫
        (I.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward f)).hom := by
  simp only [moduleSpecDerivedPushforwardModelIsoOfCounit, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, Iso.symm_hom, asIso_inv]

/-- For a qcqs morphism and quasicoherent coefficient, the proved original counit theorem
turns any actual native derived global-sections model into an actual native direct-image model.
No exactness of global sections or injectivity of pushed terms is assumed. -/
def moduleSpecDerivedPushforwardModelIso [QuasiCompact f] [QuasiSeparated f]
    [M.IsQuasicoherent] :
    DerivedCategory.Plus.Q.obj ((tilde.functor R).mapCochainComplexPlus.obj P) ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) :=
  moduleSpecDerivedPushforwardModelIsoOfCounit f I P e
    (moduleResolutionPushforwardTildeCounit_quasiIso f M I)

end AlgebraicGeometry.Scheme.Cohomology
