/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.SeparatedResolution
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.DerivedModelCounit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.InjectiveResolution
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Transporting an actual derived global-sections model to an affine-base direct image

The original spectrum-section comparison identifies sections of the actual
pushed injective resolution with the original structural-ring sections.
Exact tilde transports an actual native derived-object comparison using its
installed derived units. The final arrow is the original tilde/sections
counit on that same pushed resolution. Its quasi-isomorphism is proved for
quasi-compact separated morphisms and quasicoherent coefficients by the existing supplier.

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
local instance separatedDerivedModelAdapterSource : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on the indicated module category. -/
local instance separatedDerivedModelAdapterModules : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

/-- The standard derived-category structure on the indicated module category. -/
local instance separatedDerivedModelAdapterTarget : HasDerivedCategory.{u + 1} (Spec R).Modules :=
  HasDerivedCategory.standard _

variable (P : CochainComplex.Plus (ModuleCat.{u} R))
  (e : DerivedCategory.Plus.Q.obj P ≅
    (moduleGlobalSectionsFunctorOfHom X
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))

/-- For a quasi-compact separated morphism and quasicoherent coefficient,
the proved original counit theorem
turns any actual native derived global-sections model into an actual native direct-image model.
No exactness of global sections or injectivity of pushed terms is assumed. -/
def moduleSpecDerivedPushforwardModelIso_of_isSeparated [QuasiCompact f] [IsSeparated f]
    [M.IsQuasicoherent] :
    DerivedCategory.Plus.Q.obj ((tilde.functor R).mapCochainComplexPlus.obj P) ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) :=
  moduleSpecDerivedPushforwardModelIsoOfCounit f I P e
    (moduleResolutionPushforwardTildeCounit_quasiIso_of_isSeparated f M I)

end AlgebraicGeometry.Scheme.Cohomology
