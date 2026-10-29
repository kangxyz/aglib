/- Diagnostic source for the existing P6 R4 kernel boundary. -/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingTorsion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.BaseChange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Conservative

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PhaseFormation

open Coefficients

universe u wMX wMS wMX' wMS' wAX wAS wAX' wAS'

attribute [local instance] hasSheafifyLarge

section ModuleTarget

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Faithful formation check for the original module-exchange conclusion. -/
theorem targetFormation (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (_hK : moduleTorsionCohomologyPlus X Λ K)
    (_h : IsIso ((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)) :
    True := True.intro

end ModuleTarget

section UnderlyingTorsion

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]

/-- Faithful formation check for the exact underlying torsion predicate. -/
theorem torsionFormation (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (_h : ∀ n : ℤ, Sheaf.IsTorsion
      ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} X) n).obj
        ((moduleDerivedUnderlying Λ X).obj K))) : True := True.intro

/-- Faithful formation check for the actual conservative functor dictionary. -/
theorem reflectionFormation
    (_h : (moduleDerivedUnderlying Λ X).ReflectsIsomorphisms) : True := True.intro

end UnderlyingTorsion

section AbelianExchange

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wAX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Faithful formation check for the original abelian exchange at underlying K. -/
theorem abelianExchangeFormation (K : DerivedCategory.Plus (ModuleSheaf X Λ))
    (_h : IsIso ((derivedBaseChangeMap f f' g g' sq.w.symm).app
      ((moduleDerivedUnderlying Λ X).obj K))) : True := True.intro

end AbelianExchange

section Cube

variable (Λ : Type (u + 1)) [Ring Λ] {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wMX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wMS'} (ModuleSheaf S' Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wAX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wAS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

/-- Faithful formation check for the exact existing whole cube proposition. -/
theorem cubeFormation (_h : HorizontalMateCubeEquation
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom
      (moduleDerivedDirectImageUnderlyingIso Λ f').hom
      (moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
      (derivedBaseChangeMap f f' g g' sq.w.symm)
      (moduleDerivedInverseImageUnderlyingIso Λ g).inv
      (moduleDerivedInverseImageUnderlyingIso Λ g').inv) : True := True.intro

end Cube

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.R4PhaseFormation
