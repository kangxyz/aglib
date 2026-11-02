/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.NatTransCone
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-! # Original section comparisons on finite open covers

Only finite limits are preserved. In particular no assertion is made that
sectionwise application of the coefficient functor preserves arbitrary sheaves.
-/

@[expose] public noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory Limits Opposite TopologicalSpace

namespace TopCat.Presheaf

variable {X : TopCat.{w}} {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

/-- A section comparison is invertible on a finite union if it is invertible
on the covering opens and their pairwise intersections. The source sheaf is
mapped by the supplied finite-limit-preserving functor, not sheafified again. -/
theorem isIso_app_iSup_of_finite {F : X.Presheaf C} {G : X.Presheaf D}
    (hF : F.IsSheaf) (hG : G.IsSheaf) (T : C ⥤ D) [PreservesFiniteLimits T]
    (α : F ⋙ T ⟶ G) {ι : Type w} [Finite ι] (U : ι → Opens X)
    (hU : ∀ i, IsIso (α.app (op (U i))))
    (hUV : ∀ i j, IsIso (α.app (op (U i ⊓ U j)))) :
    IsIso (α.app (op (iSup U))) := by
  classical
  let := Fintype.ofFinite ι
  let c := (Pairwise.cocone U).op
  let h₁ : IsLimit (F.mapCone c) := (hF.isSheafPairwiseIntersections U).some
  let h₂ : IsLimit (G.mapCone c) := (hG.isSheafPairwiseIntersections U).some
  let h₃ : IsLimit ((F ⋙ T).mapCone c) :=
    (isLimitOfPreserves T h₁).ofIsoLimit (Functor.mapConeMapCone c)
  let : ∀ j, IsIso (α.app (((Pairwise.diagram U).op).obj j)) := by
    intro j
    change IsIso (α.app (op ((Pairwise.diagram U).obj j.unop)))
    cases j.unop with
    | single i => exact hU i
    | pair i j => exact hUV i j
  exact α.isIso_app_cone c h₃ h₂

end TopCat.Presheaf
