/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.GraphClosure
public import Aglib.AlgebraicGeometry.Limits.FiniteProducts.BaseChange

/-!
# Finite products of actual graph closures

Each component is the original scheme-theoretic graph image. The source is its
finite native product over `X`; the target is the finite native product of the
original target schemes over `S`. The original pair of projections is a closed
immersion into `X` times that target. Properness and dense-open surjectivity
are inherited from the original component projections.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Chow.GraphProduct

variable {X S : Scheme.{u}} (f : X ⟶ S) {n : ℕ} (P : Fin n → Over S)
  (U : Fin n → X.Opens) (h : ∀ i, (U i).toScheme ⟶ (P i).left)
  (w : ∀ i, (U i).ι ≫ f = h i ≫ (P i).hom)

/-- The original graph closure, regarded over its original source. -/
def componentOver (i : Fin n) : Over X :=
  Over.mk (GraphClosure.toSource f (P i).hom (U i) (h i) (w i))

/-- The original graph image inclusion, with the two native pullback factors exchanged. -/
def componentMap (i : Fin n) :
    componentOver f P U h w i ⟶ (Over.pullback f).obj (P i) :=
  Over.homMk
    ((GraphClosure.graph f (P i).hom (U i) (h i) (w i)).imageι ≫
      (pullbackSymmetry f (P i).hom).hom)
    (by simp [componentOver, GraphClosure.toSource])

instance componentMap_isClosedImmersion (i : Fin n) :
    IsClosedImmersion (componentMap f P U h w i).left := by
  dsimp [componentMap]
  infer_instance

/-- The finite product of the actual graph closures over `X`. -/
def modelOver : Over X := finiteProductOver (componentOver f P U h w)

/-- The underlying native scheme of the finite graph product. -/
abbrev model : Scheme.{u} := (modelOver f P U h w).left

/-- The finite native product of the original targets over `S`. -/
abbrev targetOver : Over S := finiteProductOver P

/-- The product of the original graph-image inclusions, using canonical native base change. -/
def overMap : modelOver f P U h w ⟶ (Over.pullback f).obj (targetOver P) :=
  finiteProductOverMap (componentMap f P U h w) ≫ (finiteProductOverPullbackIso f P).inv

instance overMap_isClosedImmersion : IsClosedImmersion (overMap f P U h w).left := by
  have := isClosedImmersion_finiteProductOverMap (componentMap f P U h w)
  dsimp only [overMap, Over.comp_left]
  infer_instance

/-- The original structure map from the finite graph product to `X`. -/
def toSource : model f P U h w ⟶ X := (modelOver f P U h w).hom

/-- The original map from the finite graph product to the finite target product. -/
def toTarget : model f P U h w ⟶ (targetOver P).left :=
  (overMap f P U h w).left ≫ pullback.fst (targetOver P).hom f

/-- The original projection to a single graph-closure factor. -/
def toComponent (i : Fin n) :
    model f P U h w ⟶ GraphClosure.closure f (P i).hom (U i) (h i) (w i) :=
  (finiteProductOverπ (componentOver f P U h w) i).left

@[reassoc (attr := simp)]
theorem overMap_map_π (i : Fin n) :
    overMap f P U h w ≫ (Over.pullback f).map (finiteProductOverπ P i) =
      finiteProductOverπ (componentOver f P U h w) i ≫ componentMap f P U h w i := by
  simp [overMap]

@[reassoc (attr := simp)]
theorem toTarget_π (i : Fin n) :
    toTarget f P U h w ≫ (finiteProductOverπ P i).left =
      toComponent f P U h w i ≫ GraphClosure.toTarget f (P i).hom (U i) (h i) (w i) := by
  have he := congrArg (fun k => k.left ≫ pullback.fst (P i).hom f)
    (overMap_map_π f P U h w i)
  simp only [Over.comp_left, Over.pullback_map_left, componentMap, Over.homMk_left] at he
  simpa only [toTarget, toComponent, GraphClosure.toTarget, Category.assoc,
    pullback.lift_fst, pullbackSymmetry_hom_comp_fst] using he

@[reassoc (attr := simp)]
theorem toComponent_toSource (i : Fin n) :
    toComponent f P U h w i ≫ GraphClosure.toSource f (P i).hom (U i) (h i) (w i) =
      toSource f P U h w :=
  (finiteProductOverπ (componentOver f P U h w) i).w

@[reassoc (attr := simp)]
theorem toSource_comp : toSource f P U h w ≫ f = toTarget f P U h w ≫ (targetOver P).hom := by
  change (modelOver f P U h w).hom ≫ f = _
  rw [← (overMap f P U h w).w]
  simp only [Over.pullback_obj_hom, toTarget, Category.assoc, pullback.condition]

/-- The literal pair of original projections into `X` times the finite target product. -/
def pair : model f P U h w ⟶ pullback f (targetOver P).hom :=
  pullback.lift (toSource f P U h w) (toTarget f P U h w) (toSource_comp f P U h w)

theorem pair_eq : pair f P U h w =
    (overMap f P U h w).left ≫ (pullbackSymmetry (targetOver P).hom f).hom := by
  apply pullback.hom_ext
  · simp only [pair, pullback.lift_fst, Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact (overMap f P U h w).w.symm
  · simp [pair, toTarget]

instance pair_isClosedImmersion : IsClosedImmersion (pair f P U h w) := by
  rw [pair_eq]
  infer_instance

@[reassoc (attr := simp)]
theorem pair_fst : pair f P U h w ≫ pullback.fst f (targetOver P).hom =
    toSource f P U h w := by
  simp [pair]

@[reassoc (attr := simp)]
theorem pair_snd : pair f P U h w ≫ pullback.snd f (targetOver P).hom =
    toTarget f P U h w := by
  simp [pair]

variable [∀ i, IsProper (P i).hom]

instance toSource_isProper : IsProper (toSource f P U h w) := by
  have (i : Fin n) : IsProper (componentOver f P U h w i).hom := by
    dsimp [componentOver]
    infer_instance
  exact isProper_finiteProductOver (componentOver f P U h w)

/-- Density of every original open makes the actual finite graph-product projection
surjective, including the empty-family identity case. -/
theorem toSource_surjective (hU : ∀ i, Dense (U i : Set X)) :
    Surjective (toSource f P U h w) := by
  have (i : Fin n) : Surjective (componentOver f P U h w i).hom :=
    GraphClosure.toSource_surjective f (P i).hom (U i) (h i) (w i) (hU i)
  exact surjective_finiteProductOver (componentOver f P U h w)

end AlgebraicGeometry.Scheme.Chow.GraphProduct
