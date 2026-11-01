/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.GeometricPullbackTriangle
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.Derived
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExactMapSquare

/-! # Geometric pullback of the original D+ localization triangle, including its connecting map -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wX' wU wU' wZ wZ'
variable {U Z X U' Z' X' : Scheme.{u}}
  (j : U ⟶ X) (i : Z ⟶ X) (j' : U' ⟶ X') (i' : Z' ⟶ X')
  (f : X' ⟶ X) (g : U' ⟶ U) (k : Z' ⟶ Z)
  [IsOpenImmersion j] [IsOpenImmersion j'] [IsClosedImmersion i] [IsClosedImmersion i']
  (hj : IsPullback g j' j f) (hi : IsPullback k i' i f)
  (Λ : Type (u + 1)) [Ring Λ]
  (hc : Set.range j = (Set.range i)ᶜ) (hc' : Set.range j' = (Set.range i')ᶜ)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]

/-- The complete original geometric triangle comparison is natural in complexes. -/
theorem moduleLocalizationComplexTrianglePullbackIso_naturality
    {K L : CochainComplex.Plus (ModuleSheaf X Λ)} (a : K ⟶ L) :
    (moduleDerivedInverseImage Λ f).mapTriangle.map
        (moduleLocalizationComplexTriangleMap j Λ i hc a) ≫
      (moduleLocalizationComplexTrianglePullbackIso j i j' i' f g k hj hi Λ hc hc' L).hom =
    (moduleLocalizationComplexTrianglePullbackIso j i j' i' f g k hj hi Λ hc hc' K).hom ≫
      moduleLocalizationComplexTriangleMap j' Λ i' hc'
        ((moduleInverseImage f Λ).mapCochainComplexPlus.map a) := by
  rw [moduleLocalizationComplexTrianglePullbackIso_hom,
    moduleLocalizationComplexTrianglePullbackIso_hom]
  exact DerivedCategory.Plus.mapTriangleOfSESPlusIso_square (moduleInverseImage f Λ)
    (moduleLocalizationComplex_shortExact j Λ i hc K)
    (moduleLocalizationComplex_shortExact j Λ i hc L)
    (moduleLocalizationComplex_shortExact j' Λ i' hc'
      ((moduleInverseImage f Λ).mapCochainComplexPlus.obj K))
    (moduleLocalizationComplex_shortExact j' Λ i' hc'
      ((moduleInverseImage f Λ).mapCochainComplexPlus.obj L))
    (moduleLocalizationComplexPullbackIso j i j' i' f g k hj hi Λ hc hc' K)
    (moduleLocalizationComplexPullbackIso j i j' i' f g k hj hi Λ hc hc' L)
    (moduleLocalizationComplexMap j Λ i hc a)
    (moduleLocalizationComplexMap j' Λ i' hc'
      ((moduleInverseImage f Λ).mapCochainComplexPlus.map a))
    (moduleLocalizationComplexPullbackIso_naturality j i j' i' f g k hj hi Λ hc hc' a)

/-- The actual full triangle comparison before localization. -/
def moduleLocalizationComplexTrianglePullbackNatIso :
    moduleLocalizationComplexTriangleFunctor j Λ i hc ⋙
      (moduleDerivedInverseImage Λ f).mapTriangle ≅
      (moduleInverseImage f Λ).mapCochainComplexPlus ⋙
        moduleLocalizationComplexTriangleFunctor j' Λ i' hc' :=
  NatIso.ofComponents (moduleLocalizationComplexTrianglePullbackIso j i j' i' f g k hj hi Λ hc hc')
    (by intro K L a
        exact moduleLocalizationComplexTrianglePullbackIso_naturality j i j' i' f g k
          hj hi Λ hc hc' a)

variable [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wU'} (ModuleSheaf U' Λ)]
  [HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [HasDerivedCategory.{wZ'} (ModuleSheaf Z' Λ)]

/-- Canonical Q descent of the entire original triangle comparison, without derived faithfulness. -/
def moduleLocalizationTrianglePullbackNatIso :
    moduleLocalizationTriangleFunctor j Λ i hc ⋙ (moduleDerivedInverseImage Λ f).mapTriangle ≅
      moduleDerivedInverseImage Λ f ⋙ moduleLocalizationTriangleFunctor j' Λ i' hc' := by
  let F := moduleInverseImage f Λ
  letI : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  let A := moduleLocalizationTriangleFunctor j Λ i hc ⋙
    (moduleDerivedInverseImage Λ f).mapTriangle
  let B := moduleDerivedInverseImage Λ f ⋙ moduleLocalizationTriangleFunctor j' Λ i' hc'
  refine Localization.liftNatIso DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso (ModuleSheaf X Λ))
      (DerivedCategory.Plus.Q ⋙ A) (DerivedCategory.Plus.Q ⋙ B) A B ?_
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleLocalizationTriangleFunctorFac j Λ i hc) _ ≪≫
    moduleLocalizationComplexTrianglePullbackNatIso j i j' i' f g k hj hi Λ hc hc' ≪≫
    Functor.isoWhiskerLeft F.mapCochainComplexPlus
      (moduleLocalizationTriangleFunctorFac j' Λ i' hc').symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso F.rightDerivedFunctorPlusUnit) _ ≪≫
    Functor.associator _ _ _

/-- Geometric inverse image preserves the actual original localization triangle on arbitrary D+
objects, including the connecting arrow and the original native open/closed vertices. -/
def moduleDerivedLocalizationTrianglePullbackIso (K : DerivedCategory.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedInverseImage Λ f).mapTriangle.obj (moduleDerivedLocalizationTriangle j Λ i hc K) ≅
      moduleDerivedLocalizationTriangle j' Λ i' hc' ((moduleDerivedInverseImage Λ f).obj K) :=
  (moduleDerivedInverseImage Λ f).mapTriangle.mapIso
      (moduleDerivedLocalizationTriangleIso j Λ i hc K).symm ≪≫
    (moduleLocalizationTrianglePullbackNatIso j i j' i' f g k hj hi Λ hc hc').app K ≪≫
    moduleDerivedLocalizationTriangleIso j' Λ i' hc' ((moduleDerivedInverseImage Λ f).obj K)
end AlgebraicGeometry.Scheme.EtaleCohomology
