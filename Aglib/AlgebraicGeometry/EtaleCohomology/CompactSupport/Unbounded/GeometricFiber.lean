/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Unbounded.GeometricStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Unbounded.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ExceptionalBaseChange

/-! # Original unbounded exceptional base change at a geometric point

The comparison is the existing canonical literal-pullback exceptional exchange,
transported by the proved module-linear stalk/sections comparison and native
homology. Every source, target, and raw compactification model stays explicit.
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

/-- Original unbounded exceptional homology at a geometric point is actual compactly supported
cohomology of the original derived pullback on the literal geometric fibre. -/
def moduleExceptionalUnboundedGeometricFiberIso (q : ℤ) :
    moduleExceptionalDirectImageUnbounded f Λ ⋙
        DerivedCategory.homologyFunctor (ModuleSheaf S Λ) q ⋙ moduleGeometricStalk Λ s ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd s f) ⋙
        moduleCompactlySupportedCohomologyUnbounded (pullback.fst s f) Λ ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q :=
  Functor.isoWhiskerLeft (moduleExceptionalDirectImageUnbounded f Λ)
      (moduleUnboundedGeometricStalkHomologyIso s Λ q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f s Λ N hN hΛ)
      (moduleUnboundedDerivedGlobalSections (Spec (.of Ω)) Λ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) q) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd s f))
      (Functor.associator _ _ _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
