/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation.Generators
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.Presentable.Limits

/-! # Compactness from an actual finite scalar-quotient presentation

Only the real, explicitly sized evaluation-continuity assumptions are used.
Native finite-colimit closure supplies quotient, finite-sum and cokernel
compactness. The original generators, relation arrow and cokernel map remain
part of the interface.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.TorsionFinitePresentation

universe k t v u

attribute [local instance] Cardinal.fact_isRegular_aleph0

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

/-- Real evaluation continuity makes the existing integer free representable compact. -/
theorem isFinitelyPresentable_freeAbelianSheaf_of_evaluation (U : C)
    (hU : PreservesFilteredColimitsOfSize.{k, k} (evaluation.{t} J U)) :
    IsFinitelyPresentable.{k} (Hypercohomology.freeAbelianSheaf.{t} J U) := by
  let : (evaluation.{t} J U).IsCardinalAccessible Cardinal.aleph0.{k} :=
    Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize.mpr hU
  exact Functor.isCardinalAccessible_of_natIso
    (freeRepresentableEvaluationIso.{t} J U).symm Cardinal.aleph0.{k}

/-- The genuine free scalar quotient is compact by native finite-colimit closure. -/
theorem isFinitelyPresentable_freeZModRepresentable_of_evaluation (n : ℕ) (U : C)
    (hU : PreservesFilteredColimitsOfSize.{k, k} (evaluation.{t} J U)) :
    IsFinitelyPresentable.{k} (freeZModRepresentable.{t} J n U) := by
  let P := Hypercohomology.freeAbelianSheaf.{t} J U
  have : IsFinitelyPresentable.{k} P :=
    isFinitelyPresentable_freeAbelianSheaf_of_evaluation J U hU
  have (j : WalkingParallelPair) :
      IsFinitelyPresentable.{k} ((parallelPair (n • 𝟙 P) 0).obj j) := by
    cases j <;> exact inferInstanceAs (IsFinitelyPresentable.{k} P)
  exact isCardinalPresentable_of_isColimit'
    (colimit.cocone (parallelPair (n • 𝟙 P) 0)) (colimit.isColimit _)
    Cardinal.aleph0.{k} ((hasCardinalLT_aleph0_iff _).mpr inferInstance)

/-- The actual finite sum of free scalar-quotient generators on the specified objects. -/
abbrev finiteFreeZMod (n : ℕ) {r : ℕ} (U : Fin r → C) :
    Sheaf J AddCommGrpCat.{max v t} :=
  ∐ fun i => freeZModRepresentable.{t} J n (U i)

/-- A finite family of continuous evaluations supplies compactness of its original finite sum. -/
theorem isFinitelyPresentable_finiteFreeZMod_of_evaluation (n : ℕ) {r : ℕ} (U : Fin r → C)
    (hU : ∀ i, PreservesFilteredColimitsOfSize.{k, k} (evaluation.{t} J (U i))) :
    IsFinitelyPresentable.{k} (finiteFreeZMod.{t} J n U) := by
  have (i : Discrete (Fin r)) :
      IsFinitelyPresentable.{k}
        ((Discrete.functor (fun j => freeZModRepresentable.{t} J n (U j))).obj i) :=
    isFinitelyPresentable_freeZModRepresentable_of_evaluation J n (U i.as) (hU i.as)
  exact isCardinalPresentable_of_isColimit'
    (colimit.cocone (Discrete.functor (fun i => freeZModRepresentable.{t} J n (U i))))
    (colimit.isColimit _) Cardinal.aleph0.{k}
    ((hasCardinalLT_aleph0_iff _).mpr inferInstance)

/-- An actual finite generator/relation cokernel presentation proves compactness of its point. -/
theorem isFinitelyPresentable_of_finiteZModPresentation (n : ℕ) {r0 r1 : ℕ}
    (U0 : Fin r0 → C) (U1 : Fin r1 → C)
    (h0 : ∀ i, PreservesFilteredColimitsOfSize.{k, k} (evaluation.{t} J (U0 i)))
    (h1 : ∀ j, PreservesFilteredColimitsOfSize.{k, k} (evaluation.{t} J (U1 j)))
    {F : Sheaf J AddCommGrpCat.{max v t}}
    (d : finiteFreeZMod.{t} J n U1 ⟶ finiteFreeZMod.{t} J n U0)
    (q : finiteFreeZMod.{t} J n U0 ⟶ F) (hdq : d ≫ q = 0)
    (hq : IsColimit (CokernelCofork.ofπ q hdq)) : IsFinitelyPresentable.{k} F := by
  have hP0 : IsFinitelyPresentable.{k} (finiteFreeZMod.{t} J n U0) :=
    isFinitelyPresentable_finiteFreeZMod_of_evaluation J n U0 h0
  have hP1 : IsFinitelyPresentable.{k} (finiteFreeZMod.{t} J n U1) :=
    isFinitelyPresentable_finiteFreeZMod_of_evaluation J n U1 h1
  have (j : WalkingParallelPair) :
      IsFinitelyPresentable.{k} ((parallelPair d 0).obj j) := by
    cases j with
    | zero =>
        change IsFinitelyPresentable.{k} (finiteFreeZMod.{t} J n U1)
        exact hP1
    | one =>
        change IsFinitelyPresentable.{k} (finiteFreeZMod.{t} J n U0)
        exact hP0
  exact isCardinalPresentable_of_isColimit' (CokernelCofork.ofπ q hdq) hq
    Cardinal.aleph0.{k} ((hasCardinalLT_aleph0_iff _).mpr inferInstance)

end CategoryTheory.Sheaf.TorsionFinitePresentation
