/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.DerivedFreeSplit

/-! A finite basis in each original degree gives the original field-unit splitting. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u w

attribute [local instance] hasSheafifyLarge

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (Λ : Type (u + 1)) [CommRing Λ]
  [HasDerivedCategory.{w} (ModuleSheaf (Spec (.of Ω)) Λ)]
  {I : Type} [Finite I] (d : I → ℤ)
  (K : DerivedCategory.Plus (ModuleSheaf (Spec (.of Ω)) Λ))
  (b : ∀ q : ℤ, Module.Basis {i : I // d i = q} Λ
    ((moduleGlobalSections (Spec (.of Ω)) Λ).obj
      ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf (Spec (.of Ω)) Λ) q).obj K)))

example : IsIso (moduleFieldDerivedFreeSplitMap Ω Λ d K b) :=
  moduleFieldDerivedFreeSplitMap_isIso Ω Λ d K b
