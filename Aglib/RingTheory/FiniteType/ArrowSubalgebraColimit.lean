/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteType.SubalgebraColimit

/-! # Simultaneous finite-type approximation of an original algebra arrow

For an arbitrary `R`-algebra map `α : A →ₐ[R] B`, one filtered index carries
finite-generated subalgebras of both original rings and the restrictions of
`α`. Both colimit cocones use the original inclusions. No injectivity,
Noetherianity, or finite-type assumption on `α`, `A`, or `B` is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Algebra.FiniteTypeSubalgebraLimit

universe u v

/-- An exhaustive monotone system of actual subalgebras has its original
inclusion cocone as colimit. This uses the existing subalgebra diagram. -/
def subalgebraCoconeIsColimitOfExhaustive
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    {J : Type v} [Preorder J] [IsFiltered J]
    (S : J → Subalgebra R A) (hS : Monotone S)
    (hcover : ∀ x : A, ∃ j, x ∈ S j) :
    IsColimit (subalgebraCocone R A S hS) := by
  let D := subalgebraDiagram R A S hS
  let C : (D ⋙ forget CommRingCat).CoconeTypes :=
    (D ⋙ forget CommRingCat).coconeTypesEquiv.symm
      ((forget CommRingCat).mapCocone (subalgebraCocone R A S hS))
  have hC : C.IsColimit := by
    refine ⟨?_, ?_⟩
    · rw [Functor.CoconeTypes.descColimitType_injective_iff_of_isFiltered']
      intro j x y h
      refine ⟨j, 𝟙 j, ?_⟩
      exact Subtype.ext h
    · intro x
      obtain ⟨j, hj⟩ := hcover x
      refine ⟨Functor.ιColimitType (D ⋙ forget CommRingCat) j ⟨x, hj⟩, ?_⟩
      exact Functor.descColimitType_ιColimitType_apply _ _ _ _
  let : ReflectsColimit D (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat)
  exact ((Functor.CoconeTypes.isColimit_iff C).mp hC).some

end Algebra.FiniteTypeSubalgebraLimit

namespace Algebra.FiniteTypeSubalgebraLimit

universe u v

variable {R : Type u} {A B : Type v} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The unique actual restriction of an algebra arrow to two supplied subalgebras. -/
def subalgebraRestriction (α : A →ₐ[R] B) (S : Subalgebra R A) (T : Subalgebra R B)
    (h : ∀ x : S, α x ∈ T) : S →ₐ[R] T :=
  (α.comp S.val).codRestrict T h

/-- Whole native natural transformation of actual inclusion diagrams,
constructed before any finite generators are substituted. -/
def subalgebraDiagramMap {J : Type v} [Preorder J]
    (S : J → Subalgebra R A) (T : J → Subalgebra R B)
    (hS : Monotone S) (hT : Monotone T)
    (α : A →ₐ[R] B) (h : ∀ j (x : S j), α x ∈ T j) :
    subalgebraDiagram R A S hS ⟶ subalgebraDiagram R B T hT where
  app j := CommRingCat.ofHom (subalgebraRestriction α (S j) (T j) (h j)).toRingHom
  naturality _ _ _ := rfl

/-- The complete original restriction transformation commutes with the
original inclusion cocones. -/
@[reassoc]
theorem subalgebraDiagramMap_cocone {J : Type v} [Preorder J]
    (S : J → Subalgebra R A) (T : J → Subalgebra R B)
    (hS : Monotone S) (hT : Monotone T)
    (α : A →ₐ[R] B) (h : ∀ j (x : S j), α x ∈ T j) (j : J) :
    (subalgebraDiagramMap S T hS hT α h).app j ≫ (subalgebraCocone R B T hT).ι.app j =
      (subalgebraCocone R A S hS).ι.app j ≫ CommRingCat.ofHom α.toRingHom := rfl

end Algebra.FiniteTypeSubalgebraLimit

namespace Algebra.FiniteTypeArrowLimit

universe u v

variable {R : Type u} {A B : Type v} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The single directed index for both ends of the original arrow. -/
abbrev Index (A B : Type v) := Finset A × Finset B

/-- Use the preorder category of the common directed index, as in the
existing subalgebra inclusion diagram, rather than the product-category instance. -/
instance indexCategory (A B : Type v) : SmallCategory (Index A B) :=
  Preorder.smallCategory _

instance indexFiltered (A B : Type v) : IsFiltered (Index A B) := by
  classical
  exact isFiltered_of_semilatticeSup_nonempty (Index A B)

/-- The source subalgebra of the original ring. -/
abbrev sourceStage (_α : A →ₐ[R] B) (s : Index A B) : Subalgebra R A :=
  FiniteTypeSubalgebraLimit.stage R A s.1

/-- The target stage contains the specified target generators and the images
of every source generator. -/
abbrev targetStage (α : A →ₐ[R] B) (s : Index A B) : Subalgebra R B :=
  Algebra.adjoin R (α '' (s.1 : Set A) ∪ (s.2 : Set B))

instance sourceStage_finiteType (α : A →ₐ[R] B) (s : Index A B) :
    Algebra.FiniteType R (sourceStage α s) := inferInstance

instance targetStage_finiteType (α : A →ₐ[R] B) (s : Index A B) :
    Algebra.FiniteType R (targetStage α s) :=
  Algebra.FiniteType.adjoin_of_finite ((s.1.finite_toSet.image α).union s.2.finite_toSet)

theorem sourceStage_monotone (α : A →ₐ[R] B) : Monotone (sourceStage α) :=
  fun _ _ h => Algebra.adjoin_mono (Finset.coe_subset.mpr h.1)

theorem targetStage_monotone (α : A →ₐ[R] B) : Monotone (targetStage α) := by
  intro s t h
  apply Algebra.adjoin_mono
  intro x hx
  rcases hx with ⟨a, ha, rfl⟩ | hb
  · exact Or.inl ⟨a, h.1 ha, rfl⟩
  · exact Or.inr (h.2 hb)

/-- The original algebra map takes every source-stage element to its target stage. -/
theorem map_mem_targetStage (α : A →ₐ[R] B) (s : Index A B)
    (x : sourceStage α s) : α x ∈ targetStage α s := by
  have h : sourceStage α s ≤ (targetStage α s).comap α := by
    apply Algebra.adjoin_le
    intro a ha
    exact Algebra.subset_adjoin (Or.inl ⟨a, ha, rfl⟩)
  exact h x.property

/-- The restriction of the original arrow, without a new algebra model. -/
def stageMap (α : A →ₐ[R] B) (s : Index A B) :
    sourceStage α s →ₐ[R] targetStage α s :=
  FiniteTypeSubalgebraLimit.subalgebraRestriction α (sourceStage α s) (targetStage α s)
    (map_mem_targetStage α s)

/-- Source-stage inclusions indexed by the common directed index. -/
def sourceDiagram (α : A →ₐ[R] B) : Index A B ⥤ CommRingCat.{v} :=
  FiniteTypeSubalgebraLimit.subalgebraDiagram R A (sourceStage α) (sourceStage_monotone α)

/-- Target-stage inclusions indexed by the same directed index. -/
def targetDiagram (α : A →ₐ[R] B) : Index A B ⥤ CommRingCat.{v} :=
  FiniteTypeSubalgebraLimit.subalgebraDiagram R B (targetStage α) (targetStage_monotone α)

/-- All restricted original arrows commute with the actual inclusions. -/
def diagramMap (α : A →ₐ[R] B) : sourceDiagram α ⟶ targetDiagram α :=
  FiniteTypeSubalgebraLimit.subalgebraDiagramMap
    (sourceStage α) (targetStage α) (sourceStage_monotone α) (targetStage_monotone α)
    α (map_mem_targetStage α)

def sourceCocone (α : A →ₐ[R] B) : Cocone (sourceDiagram α) :=
  FiniteTypeSubalgebraLimit.subalgebraCocone R A (sourceStage α) (sourceStage_monotone α)

def targetCocone (α : A →ₐ[R] B) : Cocone (targetDiagram α) :=
  FiniteTypeSubalgebraLimit.subalgebraCocone R B (targetStage α) (targetStage_monotone α)

/-- The source colimit is the unchanged source algebra. -/
def sourceCoconeIsColimit (α : A →ₐ[R] B) : IsColimit (sourceCocone α) := by
  apply FiniteTypeSubalgebraLimit.subalgebraCoconeIsColimitOfExhaustive
  intro x
  exact ⟨({x}, ∅), Algebra.subset_adjoin (by simp)⟩

/-- The target colimit is the unchanged target algebra. -/
def targetCoconeIsColimit (α : A →ₐ[R] B) : IsColimit (targetCocone α) := by
  apply FiniteTypeSubalgebraLimit.subalgebraCoconeIsColimitOfExhaustive
  intro x
  exact ⟨(∅, {x}), Algebra.subset_adjoin (Or.inr (by simp))⟩

/-- The colimit arrow is literally the supplied original arrow. -/
@[reassoc (attr := simp)]
theorem diagramMap_cocone (α : A →ₐ[R] B) (s : Index A B) :
    (diagramMap α).app s ≫ (targetCocone α).ι.app s =
      (sourceCocone α).ι.app s ≫ CommRingCat.ofHom α.toRingHom :=
  FiniteTypeSubalgebraLimit.subalgebraDiagramMap_cocone
    (sourceStage α) (targetStage α) (sourceStage_monotone α) (targetStage_monotone α)
    α (map_mem_targetStage α) s

/-- Source inclusion retains the original coefficient map. -/
@[simp]
theorem sourceCocone_algebraMap (α : A →ₐ[R] B) (s : Index A B) (r : R) :
    ((sourceCocone α).ι.app s).hom (algebraMap R (sourceStage α s) r) =
      algebraMap R A r := rfl

/-- Target inclusion retains the original coefficient map. -/
@[simp]
theorem targetCocone_algebraMap (α : A →ₐ[R] B) (s : Index A B) (r : R) :
    ((targetCocone α).ι.app s).hom (algebraMap R (targetStage α s) r) =
      algebraMap R B r := rfl

end Algebra.FiniteTypeArrowLimit
