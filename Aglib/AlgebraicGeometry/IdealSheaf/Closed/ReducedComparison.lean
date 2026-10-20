/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedFactor

/-!
# Reduced closed subschemes with equal support

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.ReducedComparison`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `d334d7bc652877b2b2694f3883bdf6b0c42588976f598ba0ab747e82f2aa835b`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v

section AlgebraicGeometry.Scheme.ReducedClosedSubscheme

/-! Two actual reduced closed subschemes with equal support are canonically
isomorphic over their ambient scheme. Applying this AFTER restriction to an
actual open retains the complementary union's full scheme structure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ReducedClosedSubscheme
variable {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
  [IsClosedImmersion i] [IsClosedImmersion j] [IsReduced C] [IsReduced D]

/-- Actual mutually inverse scheme maps, not a support-only identification. -/
def of_range_eq (h : Set.range i = Set.range j) : C ≅ D where
  hom := liftReducedToClosed j i h.le
  inv := liftReducedToClosed i j h.ge
  hom_inv_id := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, liftReducedToClosed_fac, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono j).mp
    simp only [Category.assoc, liftReducedToClosed_fac, Category.id_comp]

@[reassoc (attr := simp)] lemma of_range_eq_hom_fac (h : Set.range i = Set.range j) :
    (of_range_eq i j h).hom ≫ j = i := liftReducedToClosed_fac j i h.le

@[reassoc (attr := simp)] lemma of_range_eq_inv_fac (h : Set.range i = Set.range j) :
    (of_range_eq i j h).inv ≫ i = j := liftReducedToClosed_fac i j h.ge

/-- Literal open pullbacks of both closed subschemes. Reducedness follows
from the actual open projections, before any comparison is formed. -/
def on_open (U : X.Opens)
    (h : U.ι ⁻¹' Set.range i = U.ι ⁻¹' Set.range j) :
    pullback i U.ι ≅ pullback j U.ι := by
  let : IsReduced (pullback i U.ι) := isReduced_of_isOpenImmersion (pullback.fst i U.ι)
  let : IsReduced (pullback j U.ι) := isReduced_of_isOpenImmersion (pullback.fst j U.ι)
  apply of_range_eq (pullback.snd i U.ι) (pullback.snd j U.ι)
  rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
  exact h

@[reassoc (attr := simp)] lemma on_open_hom_snd (U : X.Opens)
    (h : U.ι ⁻¹' Set.range i = U.ι ⁻¹' Set.range j) :
    (on_open i j U h).hom ≫ pullback.snd j U.ι = pullback.snd i U.ι := by
  simp only [on_open, of_range_eq_hom_fac]

@[reassoc (attr := simp)] lemma on_open_hom_original (U : X.Opens)
    (h : U.ι ⁻¹' Set.range i = U.ι ⁻¹' Set.range j) :
    (on_open i j U h).hom ≫ pullback.fst j U.ι ≫ j = pullback.fst i U.ι ≫ i := by
  rw [pullback.condition, on_open_hom_snd_assoc, ← pullback.condition]

/-- Structural maps to any fixed base are retained by the same comparison. -/
def on_open_over {B : Scheme.{u}} (b : X ⟶ B) (U : X.Opens)
    (h : U.ι ⁻¹' Set.range i = U.ι ⁻¹' Set.range j) :
    Over.mk (pullback.snd i U.ι ≫ U.ι ≫ b) ≅
      Over.mk (pullback.snd j U.ι ≫ U.ι ≫ b) :=
  Over.isoMk (on_open i j U h) (by simp)

end AlgebraicGeometry.Scheme.ReducedClosedSubscheme

end -- noncomputable section
end AlgebraicGeometry.Scheme.ReducedClosedSubscheme

section AlgebraicGeometry.Scheme.ReducedClosedIntersection

/-! Replacing a closed scheme by a reduced closed scheme with the same support
inside an intersection which is already proved reduced. No reducedness of the
larger ambient closed scheme is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ReducedClosedIntersection
variable {C D E X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X) (e : E ⟶ X)
  [hjClosed : IsClosedImmersion j] [IsClosedImmersion e] [IsReduced D]
  (h : Set.range j = Set.range e)

def factor : D ⟶ E := liftReducedToClosed e j h.le

omit hjClosed in
@[reassoc (attr := simp)] lemma factor_fac [IsClosedImmersion j] : factor j e h ≫ e = j :=
  liftReducedToClosed_fac e j h.le

instance factor_closedImmersion : IsClosedImmersion (factor j e h) := by
  let : IsClosedImmersion (factor j e h ≫ e) := by rw [factor_fac]; infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ e

instance factor_surjective : Surjective (factor j e h) := by
  constructor
  intro y
  obtain ⟨x, hx⟩ := h.ge ⟨y, rfl⟩
  refine ⟨x, e.isClosedEmbedding.injective ?_⟩
  have hf := congrArg (fun f : D ⟶ X => f x) (factor_fac j e h)
  exact hf.trans hx

def intersectionMap : pullback i j ⟶ pullback i e :=
  pullback.lift (pullback.fst i j) (pullback.snd i j ≫ factor j e h) (by
    rw [Category.assoc, factor_fac]; exact pullback.condition)

@[reassoc (attr := simp)] lemma intersectionMap_fst :
    intersectionMap i j e h ≫ pullback.fst i e = pullback.fst i j := pullback.lift_fst ..

@[reassoc (attr := simp)] lemma intersectionMap_snd :
    intersectionMap i j e h ≫ pullback.snd i e = pullback.snd i j ≫ factor j e h :=
  pullback.lift_snd ..

lemma intersectionMap_square : IsPullback (intersectionMap i j e h)
    (pullback.snd i j) (pullback.snd i e) (factor j e h) := by
  have H : IsPullback (intersectionMap i j e h ≫ pullback.fst i e)
      (pullback.snd i j) i (factor j e h ≫ e) := by
    simpa only [intersectionMap_fst, factor_fac] using IsPullback.of_hasPullback i j
  exact H.of_right (intersectionMap_snd i j e h) (IsPullback.of_hasPullback i e)

instance intersectionMap_closedImmersion : IsClosedImmersion (intersectionMap i j e h) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (intersectionMap_square i j e h).flip inferInstance

instance intersectionMap_surjective : Surjective (intersectionMap i j e h) :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (intersectionMap_square i j e h).flip inferInstance

/-- Only the computed larger INTERSECTION is required to be reduced. -/
instance intersectionMap_isIso [IsReduced (pullback i e)] : IsIso (intersectionMap i j e h) :=
  isIso_of_isClosedImmersion_of_surjective _

def intersectionIso [IsReduced (pullback i e)] : pullback i j ≅ pullback i e :=
  asIso (intersectionMap i j e h)

@[reassoc (attr := simp)] lemma intersectionIso_hom_fst [IsReduced (pullback i e)] :
    (intersectionIso i j e h).hom ≫ pullback.fst i e = pullback.fst i j :=
  intersectionMap_fst ..

/-- The same comparison retains the actual component's structural map. -/
def intersectionOverIso {B : Scheme.{u}} (b : C ⟶ B) [IsReduced (pullback i e)] :
    Over.mk (pullback.fst i j ≫ b) ≅ Over.mk (pullback.fst i e ≫ b) :=
  Over.isoMk (intersectionIso i j e h) (by simp)

end AlgebraicGeometry.Scheme.ReducedClosedIntersection

end -- noncomputable section
end AlgebraicGeometry.Scheme.ReducedClosedIntersection
