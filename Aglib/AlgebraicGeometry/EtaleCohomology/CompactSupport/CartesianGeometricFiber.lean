/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.DerivedGeometricStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.BoundedBelow
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.SinglePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CartesianBaseChange

/-! # Compact support on a given Cartesian geometric fibre

The existing given-Cartesian exceptional exchange is followed by the same
module stalk/sections bridge and actual bounded-below derived sections.
Its ordinary single specialization retains the specified coefficient map on
the given fibre. Coefficients are intrinsically torsion over an arbitrary
commutative ring, without a common annihilator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM wX' wΩ wN wR wΛ wY wP

variable {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S)
  (Λ : Type (u + 1)) [CommRing Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback s f) Λ)]
  [HasDerivedCategory.{wΩ} (ModuleSheaf (Spec (.of Ω)) Λ)]
  [HasDerivedCategory.{wΛ} (ModuleCat.{u + 1} Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst s f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback s C.p) Λ)]

variable {Y : Scheme.{u}} (a : Y ⟶ Spec (.of Ω)) (b : Y ⟶ X)
  (h : IsPullback a b s f) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [presentationModels : ∀ C : Hom.DenseCompactification a,
    HasDerivedCategory.{wP} (ModuleSheaf C.Xbar Λ)]

/-- Bounded-below exceptional homology is actual compact support of the native
inverse image on the specified Cartesian geometric fibre. -/
def moduleExceptionalCartesianGeometricFiberIso (q : ℤ) :
    moduleExceptionalDirectImagePlus f Λ ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleSheaf S Λ) q ⋙ moduleGeometricStalk Λ s ≅
      moduleDerivedInverseImageTorsion b Λ ⋙ moduleCompactlySupportedCohomologyPlus a Λ ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q :=
  Functor.isoWhiskerLeft (moduleExceptionalDirectImagePlus f Λ)
      (moduleGeometricStalkHomologyIso s Λ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty f a s b h.flip Λ)
      (moduleDerivedGlobalSections (Spec (.of Ω)) Λ ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion b Λ)
      (Functor.associator _ _ _).symm

/-- The original ordinary torsion coefficient is pulled back along the given
map on the given Cartesian presentation. -/
def moduleHigherExceptionalCartesianFiberIso (q : ℤ) :
    moduleHigherExceptionalDirectImage f Λ q ⋙ moduleGeometricStalk Λ s ≅
      moduleTorsionCoefficientInverseImage b Λ ⋙ moduleCompactlySupportedCohomology a Λ q :=
  Functor.isoWhiskerLeft (moduleTorsionSingle X Λ 0)
      (moduleExceptionalCartesianGeometricFiberIso f s Λ a b h q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleTorsionSingleInverseImageIso b Λ 0)
      (moduleCompactlySupportedCohomologyPlus a Λ ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q) ≪≫
    Functor.associator _ _ _

/-- The specified-fibre comparison is natural in the original fixed-ring
morphism between internally torsion coefficient sheaves. -/
theorem moduleHigherExceptionalCartesianFiberIso_naturality (q : ℤ)
    {F G : (moduleTorsionCoefficients X Λ).FullSubcategory} (φ : F ⟶ G) :
    (moduleHigherExceptionalDirectImage f Λ q ⋙ moduleGeometricStalk Λ s).map φ ≫
        (moduleHigherExceptionalCartesianFiberIso f s Λ a b h q).hom.app G =
      (moduleHigherExceptionalCartesianFiberIso f s Λ a b h q).hom.app F ≫
        (moduleTorsionCoefficientInverseImage b Λ ⋙
          moduleCompactlySupportedCohomology a Λ q).map φ :=
  (moduleHigherExceptionalCartesianFiberIso f s Λ a b h q).hom.naturality φ

end AlgebraicGeometry.Scheme.EtaleCohomology
