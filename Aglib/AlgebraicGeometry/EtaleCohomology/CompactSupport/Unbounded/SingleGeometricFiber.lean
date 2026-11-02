/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Unbounded.GeometricFiber

/-! # Ordinary coefficient naturality of actual unbounded compact-support fibres

The original native single functor and exact inverse-image single comparison
turn the same original unbounded exceptional exchange into the ordinary
coefficient fibre law. Naturality is in module-sheaf morphisms over the fixed
coefficient ring, not change of scalar ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM wX' wΩ wN wR wΛ

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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The actual original ordinary coefficient appears on the geometric fibre. -/
def moduleExceptionalUnboundedSingleGeometricFiberIso (q : ℤ) :
    DerivedCategory.singleFunctor (ModuleSheaf X Λ) 0 ⋙
        moduleExceptionalDirectImageUnbounded f Λ ⋙
          DerivedCategory.homologyFunctor (ModuleSheaf S Λ) q ⋙ moduleGeometricStalk Λ s ≅
      moduleInverseImage (pullback.snd s f) Λ ⋙
        DerivedCategory.singleFunctor (ModuleSheaf (pullback s f) Λ) 0 ⋙
          moduleCompactlySupportedCohomologyUnboundedHomology (pullback.fst s f) Λ q :=
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor (ModuleSheaf X Λ) 0)
      (moduleExceptionalUnboundedGeometricFiberIso f s Λ N hN hΛ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((moduleInverseImage (pullback.snd s f) Λ).mapDerivedCategorySingleFunctor 0)
      (moduleCompactlySupportedCohomologyUnboundedHomology (pullback.fst s f) Λ q) ≪≫
    Functor.associator _ _ _

/-- The fibre comparison retains naturality in each actual ordinary coefficient morphism. -/
theorem moduleExceptionalUnboundedSingleGeometricFiberIso_naturality (q : ℤ)
    {F G : ModuleSheaf X Λ} (φ : F ⟶ G) :
    (DerivedCategory.singleFunctor (ModuleSheaf X Λ) 0 ⋙
      moduleExceptionalDirectImageUnbounded f Λ ⋙
        DerivedCategory.homologyFunctor (ModuleSheaf S Λ) q ⋙ moduleGeometricStalk Λ s).map φ ≫
          (moduleExceptionalUnboundedSingleGeometricFiberIso f s Λ N hN hΛ q).hom.app G =
      (moduleExceptionalUnboundedSingleGeometricFiberIso f s Λ N hN hΛ q).hom.app F ≫
        (moduleInverseImage (pullback.snd s f) Λ ⋙
          DerivedCategory.singleFunctor (ModuleSheaf (pullback s f) Λ) 0 ⋙
            moduleCompactlySupportedCohomologyUnboundedHomology (pullback.fst s f) Λ q).map φ :=
  (moduleExceptionalUnboundedSingleGeometricFiberIso f s Λ N hN hΛ q).hom.naturality φ

end AlgebraicGeometry.Scheme.EtaleCohomology
