/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Composition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleInverseImageCoherence
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.CompositionPredicate

/-! # Associativity of the original native inverse-image compositors -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wT wV
variable (Λ : Type (u + 1)) [Ring Λ]

/-- The original native inverse-image compositors associate. Exact inverse images
supply homology preservation; no open-immersion or injective-preservation hypothesis
is imposed. The regular predicate retains the original equality transport. -/
theorem moduleDerivedInverseImageCompIso_assoc {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T)
    [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
    [HasDerivedCategory.{wV} (ModuleSheaf V Λ)] :
    Functor.CompositionAssociates
      (eqToIso (congrArg (fun k : V ⟶ X => moduleDerivedInverseImage Λ k)
        (Category.assoc h g f)))
      (moduleDerivedInverseImageCompIso Λ f (h ≫ g))
      (moduleDerivedInverseImageCompIso Λ g h)
      (moduleDerivedInverseImageCompIso Λ (g ≫ f) h)
      (moduleDerivedInverseImageCompIso Λ f g) := by
  exact Functor.rightDerivedFunctorPlus_compositionAssociates
    (moduleInverseImage f Λ) (moduleInverseImage g Λ) (moduleInverseImage h Λ)
    (moduleInverseImage (g ≫ f) Λ) (moduleInverseImage (h ≫ g) Λ)
    (moduleInverseImage ((h ≫ g) ≫ f) Λ) (moduleInverseImage (h ≫ (g ≫ f)) Λ)
    (eqToIso (congrArg (fun k : V ⟶ X => moduleInverseImage k Λ) (Category.assoc h g f)))
    (moduleInverseImageCompIso Λ f (h ≫ g)) (moduleInverseImageCompIso Λ g h)
    (moduleInverseImageCompIso Λ (g ≫ f) h) (moduleInverseImageCompIso Λ f g)
    (moduleInverseImageCompIso_assoc Λ f g h)
    (eqToIso (congrArg (fun k : V ⟶ X => moduleDerivedInverseImage Λ k)
        (Category.assoc h g f)))
    (Functor.rightDerivedFunctorPlusIso_eqToIso _ _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
