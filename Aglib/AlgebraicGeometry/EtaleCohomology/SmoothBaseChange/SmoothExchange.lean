/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.PolynomialQcqsExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AllowedFromLine

/-! # Proposed original smooth base-change endpoints

These source drafts retain the original maps and independent derived worlds.
Acceptance requires the full original qcqs source-cover chain, not merely the
already accepted affine-source polynomial theorem.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u dX dS dX' dS'
attribute [local instance] hasSheafifyLarge

/-- Original higher smooth base change on base-invertible torsion coefficients. -/
theorem higherBaseChangeMap_smooth_allowed_isIso
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (H : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Smooth g]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsBaseInvertibleTorsion S F) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' H.w.symm q).app F) :=
  higherBaseChangeMap_smooth_allowed_isIso_of_line uniformHigherBaseChange_polynomial
    f f' g g' H F hF q

/-- Original D+ smooth base change, with four independent derived worlds. -/
theorem derivedBaseChangeMap_smooth_allowed_isIso
    {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (H : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f] [Smooth g]
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X))
    (hK : ∀ i : ℤ, IsBaseInvertibleTorsion S
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) i).obj K)) :
    IsIso ((derivedBaseChangeMap f f' g g' H.w.symm).app K) :=
  derivedBaseChangeMap_smooth_allowed_isIso_of_line uniformHigherBaseChange_polynomial
    f f' g g' H K hK

end AlgebraicGeometry.Scheme.EtaleCohomology
