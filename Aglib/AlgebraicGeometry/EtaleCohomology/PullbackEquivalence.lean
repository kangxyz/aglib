/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.Algebra.Homology.DerivedCategory.Ext.Equivalence

/-!
# Bijectivity of original pullback under an actual inverse-image equivalence

The original exact-functor map and constant-integer transport are retained.
Source and target Ext universes are independent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

/-- An equivalence of the original inverse-image functor makes original pullback bijective. -/
theorem cohomologyPullback_bijective_of_isEquivalence
    {X S : Scheme.{u}} (f : S ⟶ X)
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    [(inverseImage f).IsEquivalence] (L : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    Function.Bijective (cohomologyPullback f L q) :=
  (inverseImage f).extPrecompMap_bijective_of_isEquivalence
    (((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) L q

/-- The original coefficient map associated to a sheaf isomorphism is bijective. -/
theorem cohomologyMapIso_bijective {X : Scheme.{u}}
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    {L M : AbelianSheaf.{u, u + 1} X} (e : L ≅ M) (q : ℕ) :
    Function.Bijective (Sheaf.H.map e.hom q) := by
  let H : AbelianSheaf.{u, u + 1} X ⥤ AddCommGrpCat.{w} :=
    Sheaf.functorH.{w, u + 1, u, u + 1} X.smallEtaleTopology q
  exact (H.mapIso e).addCommGroupIsoToAddEquiv.bijective

end AlgebraicGeometry.Scheme.EtaleCohomology
