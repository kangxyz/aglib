/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.NoncommutativeScalars
public import Aglib.Algebra.Category.ModuleCat.Sheaf.UnderlyingExact
public import Aglib.Algebra.Module.FiniteExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-! # Left-Noetherian finite-generation closure for original sheaf cohomology

The original same-degree cohomology maps are exact and left-linear over an
arbitrary ring. Left Noetherianity supplies finite generation of the middle
module from the outer modules. Neither commutativity nor finite additive
coefficient groups are assumed.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace ModuleCat.Sheaf

universe u v r e
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]
attribute [local instance] hasSheafify

/-- Exactness of the original same-degree maps, with noncommutative left scalars. -/
theorem cohomologyOfRing_exact (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R)))
    (hS : S.ShortExact) (q : ℕ) :
    Function.Exact ((cohomologyOfRing J R q).map S.f).hom
      ((cohomologyOfRing J R q).map S.g).hom :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (CategoryTheory.Sheaf.H.longSequence_exact₂' (hS.map_of_exact (underlying R J)) q)

/-- Left-Noetherian finite outer cohomology modules imply a finite middle module
for the same original coefficients and actual scalar actions. -/
theorem finite_cohomologyOfRing_of_shortExact [IsNoetherianRing R]
    (S : ShortComplex (Sheaf J (ModuleCat.{max u v} R))) (hS : S.ShortExact) (q : ℕ)
    [Module.Finite R ((cohomologyOfRing J R q).obj S.X₁)]
    [Module.Finite R ((cohomologyOfRing J R q).obj S.X₃)] :
    Module.Finite R ((cohomologyOfRing J R q).obj S.X₂) :=
  Module.Finite.of_exact_of_noetherian (cohomologyOfRing_exact J R S hS q)

end ModuleCat.Sheaf
