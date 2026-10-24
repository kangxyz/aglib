/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InverseLimit.Predecessors
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Nested predecessor limits

An initial segment of an initial segment is canonically the original smaller
initial segment. The native limit isomorphism also identifies the original
stage-to-limit comparison maps, so full-limit surjectivity transports honestly.
-/

@[expose] public noncomputable section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex.InverseLimit

variable {J : Type w} [PartialOrder J]

/-- Flatten a nested strict initial segment, retaining the original index. -/
def nestedPredecessorOrderIso (i : J) (j : Set.Iio i) : Set.Iio j ≃o Set.Iio j.val where
  toFun k := ⟨k.val.val, k.property⟩
  invFun k := ⟨⟨k.val, lt_trans k.property j.property⟩, k.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

variable (F : Jᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℤ)

/-- The two actual restricted diagrams coincide under the initial-segment equivalence. -/
def nestedDiagramIso (i : J) (j : Set.Iio i) :
    (nestedPredecessorOrderIso i j).equivalence.op.functor ⋙ predecessors F j.val ≅
      predecessors (predecessors F i) j :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    change F.map _ ≫ 𝟙 _ = 𝟙 _ ≫ F.map _
    simp only [Category.comp_id, Category.id_comp]
    congr 1)

variable [∀ (i : J) (n : ℤ), HasLimit
    (predecessors F i ⋙ HomologicalComplex.eval AddCommGrpCat (.up ℤ) n)]

instance hasLimit_evaluated_nested (i : J) (j : Set.Iio i) (n : ℤ) :
    HasLimit (predecessors (predecessors F i) j ⋙
      HomologicalComplex.eval AddCommGrpCat (.up ℤ) n) := by
  let e := (nestedPredecessorOrderIso i j).equivalence.op
  have : HasLimit (e.functor ⋙ (predecessors F j.val ⋙
      HomologicalComplex.eval AddCommGrpCat (.up ℤ) n)) :=
    Limits.hasLimit_equivalence_comp e
  exact hasLimit_of_iso (Functor.isoWhiskerRight (nestedDiagramIso F i j)
    (HomologicalComplex.eval AddCommGrpCat (.up ℤ) n))

/-- Native limit comparison for the entire nested predecessor diagram. -/
def nestedLimitIso (i : J) (j : Set.Iio i) :
    limit (predecessors (predecessors F i) j) ≅ limit (predecessors F j.val) :=
  HasLimit.isoOfEquivalence (nestedPredecessorOrderIso i j).equivalence.op
    (nestedDiagramIso F i j)

set_option backward.isDefEq.respectTransparency false in
/-- The native isomorphism preserves the original full-limit comparison map. -/
lemma predecessorComparison_nested (i : J) (j : Set.Iio i) :
    predecessorComparison F j.val ≫ (nestedLimitIso F i j).inv =
      predecessorComparison (predecessors F i) j := by
  apply limit.hom_ext
  intro k
  dsimp only [nestedLimitIso]
  rw [Category.assoc, HasLimit.isoOfEquivalence_inv_π, ← Category.assoc,
    predecessorComparison_π, predecessorComparison_π]
  simp only [nestedDiagramIso, NatIso.ofComponents_hom_app, Iso.refl_hom]
  rfl

/-- Surjectivity onto the full predecessor limit survives restriction to an initial segment. -/
lemma predecessorComparison_nested_surjective (i : J) (j : Set.Iio i) (n : ℤ)
    (h : Function.Surjective ((predecessorComparison F j.val).f n)) :
    Function.Surjective ((predecessorComparison (predecessors F i) j).f n) := by
  rw [← predecessorComparison_nested]
  exact (ConcreteCategory.bijective_of_isIso ((nestedLimitIso F i j).inv.f n)).surjective.comp h

end CochainComplex.InverseLimit
