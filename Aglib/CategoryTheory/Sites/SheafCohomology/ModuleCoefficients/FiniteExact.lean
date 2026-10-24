/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.UnderlyingExact
public import Aglib.Algebra.Module.FiniteExact
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantScalars
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Finite-middle original cohomology for actual module sheaves

Native short exact sequences of actual `ModuleCat`-valued sheaves yield exact
pairs of original same-degree cohomology maps, linear for the original scalar
actions. Over a Noetherian coefficient ring, finite outer cohomology modules
therefore imply a finite middle module. No connecting-map linearity is needed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat.Sheaf

universe u v r e

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [CommRing R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

attribute [local instance] hasSheafify

/-- The literal original same-degree coefficient maps are exact for a native
short exact sequence of actual module sheaves. -/
theorem cohomology_exact (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R)))
    (hS : S.ShortExact) (q : ℕ) :
    Function.Exact ((cohomology J R q).map S.f).hom ((cohomology J R q).map S.g).hom :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (CategoryTheory.Sheaf.H.longSequence_exact₂' (hS.map_of_exact (underlying R J)) q)

/-- Finite outer original cohomology modules imply a finite middle module,
retaining the actual coefficient-ring action and unchanged original carriers. -/
theorem finite_cohomology_of_shortExact [IsNoetherianRing R]
    (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))) (hS : S.ShortExact) (q : ℕ)
    [Module.Finite R ((cohomology J R q).obj S.X₁)]
    [Module.Finite R ((cohomology J R q).obj S.X₃)] :
    Module.Finite R ((cohomology J R q).obj S.X₂) :=
  Module.Finite.of_exact_of_noetherian (cohomology_exact J R S hS q)

end ModuleCat.Sheaf
