/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Unbounded.GeometricStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Unbounded.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianBaseChange

/-! # Actual given Cartesian presentations of unbounded compact-support fibres

The accepted given-Cartesian exceptional exchange already contains the native
pullback source isomorphism and original source transport. Whiskering that same
exchange by the proved module stalk/sections bridge gives actual compact support
on the specified fibre, with its specified coefficient map. The literal-fibre
proof is not reconstructed, and independent literal/presentation models remain.
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
  (sq : IsPullback b a f s) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
  [HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [presentationModels : ∀ C : Hom.DenseCompactification a,
    HasDerivedCategory.{wP} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Original unbounded exceptional homology at a geometric point is actual compactly supported
cohomology of the original derived pullback on the specified Cartesian geometric fibre. -/
def moduleExceptionalUnboundedCartesianGeometricFiberIso (q : ℤ) :
    moduleExceptionalDirectImageUnbounded f Λ ⋙
        DerivedCategory.homologyFunctor (ModuleSheaf S Λ) q ⋙ moduleGeometricStalk Λ s ≅
      moduleUnboundedDerivedInverseImage Λ b ⋙
        moduleCompactlySupportedCohomologyUnbounded a Λ ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q :=
  Functor.isoWhiskerLeft (moduleExceptionalDirectImageUnbounded f Λ)
      (moduleUnboundedGeometricStalkHomologyIso s Λ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty f a s b sq Λ N hN hΛ)
      (moduleUnboundedDerivedGlobalSections (Spec (.of Ω)) Λ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ b)
      (Functor.associator _ _ _).symm

/-- The actual original ordinary coefficient appears on the geometric fibre. -/
def moduleExceptionalUnboundedSingleCartesianGeometricFiberIso (q : ℤ) :
    DerivedCategory.singleFunctor (ModuleSheaf X Λ) 0 ⋙
        moduleExceptionalDirectImageUnbounded f Λ ⋙
          DerivedCategory.homologyFunctor (ModuleSheaf S Λ) q ⋙ moduleGeometricStalk Λ s ≅
      moduleInverseImage b Λ ⋙
        DerivedCategory.singleFunctor (ModuleSheaf Y Λ) 0 ⋙
          moduleCompactlySupportedCohomologyUnboundedHomology a Λ q :=
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleSheaf X Λ) 0)
      (moduleExceptionalUnboundedCartesianGeometricFiberIso f s Λ a b sq N hN hΛ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((moduleInverseImage b Λ).mapDerivedCategorySingleFunctor 0)
      (moduleCompactlySupportedCohomologyUnboundedHomology a Λ q) ≪≫
    Functor.associator _ _ _

/-- The fibre comparison retains naturality in each actual ordinary coefficient morphism. -/
theorem moduleExceptionalUnboundedSingleCartesianGeometricFiberIso_naturality (q : ℤ)
    {F G : ModuleSheaf X Λ} (φ : F ⟶ G) :
    (DerivedCategory.singleFunctor (ModuleSheaf X Λ) 0 ⋙
      moduleExceptionalDirectImageUnbounded f Λ ⋙
        DerivedCategory.homologyFunctor (ModuleSheaf S Λ) q ⋙ moduleGeometricStalk Λ s).map φ ≫
          (moduleExceptionalUnboundedSingleCartesianGeometricFiberIso
            f s Λ a b sq N hN hΛ q).hom.app G =
      (moduleExceptionalUnboundedSingleCartesianGeometricFiberIso
        f s Λ a b sq N hN hΛ q).hom.app F ≫
        (moduleInverseImage b Λ ⋙
          DerivedCategory.singleFunctor (ModuleSheaf Y Λ) 0 ⋙
            moduleCompactlySupportedCohomologyUnboundedHomology a Λ q).map φ :=
  (moduleExceptionalUnboundedSingleCartesianGeometricFiberIso
    f s Λ a b sq N hN hΛ q).hom.naturality φ

end AlgebraicGeometry.Scheme.EtaleCohomology
