/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionRange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology

/-!
# Torsion cohomology under the original derived underlying functor

The installed homology comparison for exact additive forgetting identifies
internal torsion in each native module homology sheaf with internal torsion
in the original abelian homology sheaf of its derived underlying object.
Consequently it identifies the actual bounded-below torsion-cohomology range.
The module and abelian derived-category universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wM wA

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wM} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wA} (AbelianSheaf.{u, u + 1} X)]

/-- The original derived underlying functor preserves and reflects internal torsion
in every native homology sheaf. -/
theorem moduleIsTorsion_homology_iff_underlying
    (K : DerivedCategory.Plus (ModuleSheaf X Λ)) (n : ℤ) :
    moduleIsTorsion X Λ
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) n).obj K) ↔
      Sheaf.IsTorsion
        ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj
          ((moduleDerivedUnderlying Λ X).obj K)) := by
  let e :
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj
          ((moduleDerivedUnderlying Λ X).obj K) ≅
        (SheafOfModules.toSheaf (constantRing X Λ)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf X Λ) n).obj K) :=
    (Functor.rightDerivedFunctorPlusHomologyIso
      (SheafOfModules.toSheaf (constantRing X Λ)) n).app K
  constructor
  · intro h
    apply Presheaf.IsLocallyTorsion.of_injective h e.hom.hom
    intro U
    exact (((sheafToPresheaf (Scheme.smallEtaleTopology X)
      AddCommGrpCat.{u + 1}).mapIso e).app U).addCommGroupIsoToAddEquiv.injective
  · intro h
    apply Presheaf.IsLocallyTorsion.of_injective h e.inv.hom
    intro U
    exact (((sheafToPresheaf (Scheme.smallEtaleTopology X)
      AddCommGrpCat.{u + 1}).mapIso e.symm).app U).addCommGroupIsoToAddEquiv.injective

/-- The actual bounded-below module torsion range is precisely internal torsion
of all original abelian homology sheaves after derived additive forgetting. -/
theorem moduleTorsionCohomologyPlus_iff_underlying
    (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    moduleTorsionCohomologyPlus X Λ K ↔
      ∀ n : ℤ, Sheaf.IsTorsion
        ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj
          ((moduleDerivedUnderlying Λ X).obj K)) := by
  constructor
  · intro h n
    exact (moduleIsTorsion_homology_iff_underlying X Λ K n).mp (h n)
  · intro h n
    exact (moduleIsTorsion_homology_iff_underlying X Λ K n).mpr (h n)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
