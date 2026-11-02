/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ModuleCohomologyComparison
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Naturality

/-! # Native affine higher-image coefficient comparison

The original affine section/cohomology comparison followed by the original
étale comparison carries the actual derived coefficient map to its original
étale cohomology coefficient map. All coefficients remain arbitrary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry.Scheme.Cohomology

universe u e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] HasExt.standard hasSheafifyLarge
  moduleComparisonEnoughSmall moduleComparisonEnoughRaised
  moduleComparisonAbWRaised moduleComparisonTypeWRaised

/-- Complete coefficient naturality for the unchanged composite of native
Zariski affine and étale absolute comparisons. -/
theorem moduleCohomologyComparison_affineSections_naturality
    {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [QuasiCompact f] [QuasiSeparated f]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (v : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N) (q : ℕ)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (x : (moduleSpecΓFunctor (R := R)).obj
      (((Scheme.Modules.pushforward f).rightDerived q).obj M)) :
    @Eq (Sheaf.H.{e} (additiveCoefficient X N) q)
      (moduleCohomologyComparison.{u, u + 1, e} X N q
        (moduleHigherDirectImageAffineSectionsLinearEquiv f N J q
          ((moduleSpecΓFunctor (R := R)).map
            (((Scheme.Modules.pushforward f).rightDerived q).map v) x)))
      (Sheaf.H.map (additiveCoefficientMap X v) q
        (moduleCohomologyComparison.{u, u + 1, e} X M q
          (moduleHigherDirectImageAffineSectionsLinearEquiv f M I q x))) := by
  have hc := moduleHigherDirectImageAffineSectionsLinearEquiv_naturality f I J
    (v := v) q x
  have hn := moduleCohomologyComparison_naturality.{u, u + 1, e} X v q
    (moduleHigherDirectImageAffineSectionsLinearEquiv f M I q x)
  exact (congrArg (moduleCohomologyComparison.{u, u + 1, e} X N q) hc).trans hn

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
