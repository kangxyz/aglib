/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.Grp.TranslationFamily
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedComparison
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.Topology.JacobsonSpace

/-!
# The actual translated incidence subscheme

For a group scheme G, a closed immersion i: Z -> G, and a parameter map
f: T -> G, the original product Z x T maps into G x T by (z,t) -> (i(z)f(t),t).
The map uses the already constructed whole translation isomorphism. It is
the actual pullback of i along (g,t) -> g/f(t), including on nonreduced tests.

On a Jacobson ambient scheme, equality of the closed-point loci of two
reduced closed subschemes supplies their canonical scheme isomorphism over
that same ambient scheme. The theta incidence argument must supply the
reducedness of both total schemes before applying this comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] {Z T : Over S}

/-- The actual translated product immersion, using the same native
cartesian product and the generic translation-family isomorphism. -/
def incidenceMorphism (i : Z ⟶ G) (f : T ⟶ G) : Z ⊗ T ⟶ G ⊗ T :=
  (i ⊗ₘ 𝟙 T) ≫ (GrpObj.translationFamily G f).hom

/-- The classifying difference map of the incidence pullback. -/
def incidenceDifference (f : T ⟶ G) : G ⊗ T ⟶ G :=
  (GrpObj.translationFamily G f).inv ≫ fst G T

@[reassoc (attr := simp)]
theorem incidenceMorphism_fst (i : Z ⟶ G) (f : T ⟶ G) :
    incidenceMorphism G i f ≫ fst G T = (fst Z T ≫ i) * (snd Z T ≫ f) := by
  simp [incidenceMorphism, MonObj.comp_mul]

@[reassoc (attr := simp)]
theorem incidenceMorphism_snd (i : Z ⟶ G) (f : T ⟶ G) :
    incidenceMorphism G i f ≫ snd G T = snd Z T := by
  simp [incidenceMorphism]

theorem incidenceDifference_eq (f : T ⟶ G) :
    incidenceDifference G f = fst G T / (snd G T ≫ f) :=
  GrpObj.translationFamily_inv_fst G f

/-- The original translated subscheme is the actual scheme pullback of i
along the inverse-translation first coordinate. -/
theorem isPullback_incidenceMorphism (i : Z ⟶ G) (f : T ⟶ G) :
    IsPullback (fst Z T).left (incidenceMorphism G i f).left i.left
      (incidenceDifference G f).left := by
  exact (GrpObj.isPullback_translationFamily G i f).map (Over.forget S)

instance isClosedImmersion_incidenceMorphism (i : Z ⟶ G) (f : T ⟶ G)
    [IsClosedImmersion i.left] : IsClosedImmersion (incidenceMorphism G i f).left :=
  MorphismProperty.of_isPullback (isPullback_incidenceMorphism G i f) inferInstance

variable (i : Z ⟶ G) (f : T ⟶ G) [IsClosedImmersion i.left]
  {E : Scheme.{u}} (j : E ⟶ (G ⊗ T).left) [IsClosedImmersion j]
  [IsReduced (Z ⊗ T).left] [IsReduced E] [JacobsonSpace (G ⊗ T).left]

/-- Closed-point comparison for the original incidence closed subscheme.
Reducedness is used only after equality of the actual closed ranges. -/
def incidenceIsoOfClosedPoints
    (h : ∀ x : (G ⊗ T).left, IsClosed ({x} : Set (G ⊗ T).left) →
      (x ∈ Set.range (incidenceMorphism G i f).left ↔ x ∈ Set.range j)) :
    (Z ⊗ T).left ≅ E := by
  have hc : Set.range (incidenceMorphism G i f).left ∩ closedPoints (G ⊗ T).left =
      Set.range j ∩ closedPoints (G ⊗ T).left := by
    ext x
    exact and_congr_left fun hx => h x hx
  have hi := (incidenceMorphism G i f).left.isClosedEmbedding.isClosed_range
  have hj := j.isClosedEmbedding.isClosed_range
  have hr : Set.range (incidenceMorphism G i f).left = Set.range j := by
    rw [← hi.closure_eq, ← hj.closure_eq,
      ← JacobsonSpace.closure_inter_closedPoints_eq_closure hi.isLocallyClosed,
      ← JacobsonSpace.closure_inter_closedPoints_eq_closure hj.isLocallyClosed, hc]
  exact ReducedClosedSubscheme.ofRangeEq (incidenceMorphism G i f).left j hr

@[reassoc (attr := simp)]
theorem incidenceIsoOfClosedPoints_hom_fac
    (h : ∀ x : (G ⊗ T).left, IsClosed ({x} : Set (G ⊗ T).left) →
      (x ∈ Set.range (incidenceMorphism G i f).left ↔ x ∈ Set.range j)) :
    (incidenceIsoOfClosedPoints G i f j h).hom ≫ j = (incidenceMorphism G i f).left := by
  simp only [incidenceIsoOfClosedPoints, ReducedClosedSubscheme.of_range_eq_hom_fac]

end AlgebraicGeometry.Scheme.Group
