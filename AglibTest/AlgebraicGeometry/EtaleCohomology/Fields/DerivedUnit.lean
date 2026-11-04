/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.DerivedUnit

/-! The original field unit represents homology at every native derived degree. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w

attribute [local instance] hasSheafifyLarge

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (Λ : Type (u + 1)) [CommRing Λ]
  [HasDerivedCategory.{w} (ModuleSheaf (Spec (.of Ω)) Λ)]

example (i : ℤ) (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ))
    (a : (moduleGlobalSections (Spec (.of Ω)) Λ).obj
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    ∃ f : (DerivedCategory.Plus.singleFunctor _ i).obj (moduleUnit (Spec (.of Ω)) Λ) ⟶ K,
      moduleFieldDerivedUnitHomologyEquiv Ω Λ i K f = a :=
  (moduleFieldDerivedUnitHomologyEquiv Ω Λ i K).surjective a

example (i : ℤ) (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ))
    (f : (DerivedCategory.Plus.singleFunctor _ i).obj (moduleUnit (Spec (.of Ω)) Λ) ⟶ K) :
    moduleFieldDerivedUnitHomologyEquiv Ω Λ i K f =
      moduleFieldDerivedUnitHomologyMap Ω Λ i K f :=
  moduleFieldDerivedUnitHomologyEquiv_apply Ω Λ i K f
