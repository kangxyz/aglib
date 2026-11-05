/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Reduction
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.AllowedDerivedExchange

/-! # The exact remaining line input for allowed-torsion smooth exchange

This assembly requires the genuine original line comparison for arbitrary
qcqs coefficient sources. An affine-source-only statement does not satisfy
its premise. The existing smooth reduction and allowed-annihilator assembly
then give the original higher and bounded-below derived comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u dX dS dX' dS'
attribute [local instance] hasSheafifyLarge

/-- The full uniform line comparison implies original smooth higher exchange
on base-invertible torsion, without a uniform coefficient annihilator. -/
theorem higherBaseChangeMap_smooth_allowed_isIso_of_line
    (hline : ∀ n : ℕ, 0 < n → ∀ R : CommRingCat.{u},
      SmoothReduction.UniformHigherBaseChange n (PolynomialLaurent.polynomialProjection R))
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (H : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Smooth g]
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsBaseInvertibleTorsion S F) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' H.w.symm q).app F) := by
  let : QuasiCompact f' := MorphismProperty.of_isPullback H inferInstance
  let : QuasiSeparated f' := MorphismProperty.of_isPullback H inferInstance
  apply higherBaseChangeMap_isIso_of_baseInvertibleTorsion_of_killed
    f f' g g' H.w.symm q ?_ F hF
  intro n hn hunit M hM
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  exact SmoothReduction.higherBaseChangeMap_smooth_isIso_of_line
    (hline n hn) f f' g g' H hunit M hM q

/-- The same full line input gives original derived smooth exchange on D+
objects with base-invertible torsion homology, in four independent worlds. -/
theorem derivedBaseChangeMap_smooth_allowed_isIso_of_line
    (hline : ∀ n : ℕ, 0 < n → ∀ R : CommRingCat.{u},
      SmoothReduction.UniformHigherBaseChange n (PolynomialLaurent.polynomialProjection R))
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
    IsIso ((derivedBaseChangeMap f f' g g' H.w.symm).app K) := by
  exact derivedBaseChangeMap_isIso_of_baseInvertibleTorsion_homology
    f f' g g' H.w.symm
    (fun F hF q => higherBaseChangeMap_smooth_allowed_isIso_of_line
      hline f f' g g' H F hF q) K hK

end AlgebraicGeometry.Scheme.EtaleCohomology
