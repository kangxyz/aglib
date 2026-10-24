/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.ConstantScalars
public import Aglib.Algebra.Module.FiniteExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Finite-module dévissage for original constant cohomology

Only the two original same-degree coefficient maps are used. Their scalar
linearity comes from the original coefficient action, and their exactness comes
from the native sheaf-cohomology long exact sequence. No connecting-map scalar
structure is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat.Sheaf

universe u v r e

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [CommRing R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

/-- Original same-degree constant-cohomology coefficient maps form an exact pair. -/
theorem constantCohomology_exact (S : ShortComplex (ModuleCat.{max u v} R))
    (hS : S.ShortExact) (q : ℕ) :
    Function.Exact ((constantCohomology J R q).map S.f).hom
      ((constantCohomology J R q).map S.g).hom := by
  let : PreservesFiniteLimits (constantSheaf J AddCommGrpCat.{max u v}) := by
    unfold constantSheaf
    infer_instance
  let : PreservesFiniteColimits (constantSheaf J AddCommGrpCat.{max u v}) := by
    unfold constantSheaf
    infer_instance
  let U : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{max u v} := forget₂ _ _
  let : PreservesColimitsOfSize.{0, 0} U :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max u v, r, 0, 0} R
  let : PreservesLimitsOfSize.{0, 0} U :=
    ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{0, 0, max u v, r}
  let : PreservesFiniteColimits U :=
    PreservesColimitsOfSize0.preservesFiniteColimits U
  let : PreservesFiniteLimits U :=
    PreservesLimitsOfSize0.preservesFiniteLimits U
  let F : ModuleCat.{max u v} R ⥤ Sheaf J AddCommGrpCat.{max u v} :=
    U ⋙ constantSheaf J AddCommGrpCat.{max u v}
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (CategoryTheory.Sheaf.H.longSequence_exact₂' (hS.map_of_exact F) q)

/-- Finite generation of the outer original cohomology modules gives finite
generation in the middle over the original Noetherian coefficient ring. -/
theorem finite_constantCohomology_of_shortExact [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{max u v} R)) (hS : S.ShortExact) (q : ℕ)
    [Module.Finite R ((constantCohomology J R q).obj S.X₁)]
    [Module.Finite R ((constantCohomology J R q).obj S.X₃)] :
    Module.Finite R ((constantCohomology J R q).obj S.X₂) :=
  Module.Finite.of_exact_of_noetherian (constantCohomology_exact J R S hS q)

end ModuleCat.Sheaf
