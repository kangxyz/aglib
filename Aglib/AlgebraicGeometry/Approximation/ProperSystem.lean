/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Actual fixed-base proper approximation systems

The native over-category diagram retains the original base. Its limiting
scheme cone has exactly the specified source and closed projections. A
cofinal tail of a closed-transition system is proper once one stage is proper.
This file packages that reduction; it does not construct an approximation
system for an arbitrary proper scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Approximation

/-- A small proper finitely presented inverse system over the original base,
with its actual limit and closed transitions and projections. -/
structure ProperFinitePresentationSystem {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The small indexing type. -/
  index : Type u
  /-- Its actual small category structure. -/
  [category : Category.{u} index]
  /-- Cofilteredness of the index. -/
  [cofiltered : IsCofiltered index]
  /-- The actual schemes and morphisms over the unchanged base. -/
  diagram : index ⥤ Over S
  /-- The actual cone over the base. -/
  cone : Cone diagram
  /-- The point is the original structural morphism. -/
  point : cone.pt = Over.mk f
  /-- The forgotten cone is a genuine scheme limit. -/
  isLimit : IsLimit ((Over.forget S).mapCone cone)
  /-- Every stage is proper over the original base. -/
  proper (i : index) : IsProper (diagram.obj i).hom
  /-- Every stage is locally finitely presented over the original base. -/
  finitePresentation (i : index) : LocallyOfFinitePresentation (diagram.obj i).hom
  /-- Every transition is a closed immersion. -/
  closedTransition {i j : index} (q : i ⟶ j) : IsClosedImmersion (diagram.map q).left
  /-- The original limit projections are closed immersions. -/
  closedProjection (i : index) : IsClosedImmersion (cone.π.app i).left

attribute [instance] ProperFinitePresentationSystem.category
  ProperFinitePresentationSystem.cofiltered ProperFinitePresentationSystem.proper
  ProperFinitePresentationSystem.finitePresentation
  ProperFinitePresentationSystem.closedTransition ProperFinitePresentationSystem.closedProjection

/-- Restrict a native closed-transition system to the cofinal tail below a
proper stage. The cone retains its original point and native limiting proof. -/
def ProperFinitePresentationSystem.ofProperStage
    {I : Type u} [Category.{u} I] [IsCofiltered I] {X S : Scheme.{u}}
    (f : X ⟶ S) (D : I ⥤ Over S) (c : Cone D)
    (hpoint : c.pt = Over.mk f) (hc : IsLimit ((Over.forget S).mapCone c))
    [∀ i, LocallyOfFinitePresentation (D.obj i).hom]
    [∀ {i j} (q : i ⟶ j), IsClosedImmersion (D.map q).left]
    [∀ i, IsClosedImmersion (c.π.app i).left]
    (i : I) [IsProper (D.obj i).hom] : ProperFinitePresentationSystem f := by
  let E : Over i ⥤ Over S := Over.forget i ⋙ D
  let d : Cone E := c.whisker (Over.forget i)
  have hd : IsLimit ((Over.forget S).mapCone d) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i)
      ((Over.forget S).mapCone c)).symm hc
  exact
    { index := Over i
      diagram := E
      cone := d
      point := hpoint
      isLimit := hd
      proper := fun j => by
        change IsProper (D.obj j.left).hom
        exact isProper_hom_of_isProper_over_map (D.map j.hom)
      finitePresentation := fun j => inferInstanceAs
        (LocallyOfFinitePresentation (D.obj j.left).hom)
      closedTransition := fun q => inferInstanceAs
        (IsClosedImmersion (D.map q.left).left)
      closedProjection := fun j => inferInstanceAs
        (IsClosedImmersion (c.π.app j.left).left) }

/-- A closed modified stage is proper over the original base, and properness
descends along the actual proper-surjective modification. -/
theorem isProper_of_closed_modified_stage {S : Scheme.{u}}
    {Y W P : Over S} (p : W ⟶ Y) (q : W ⟶ P) (Z : Over Y.left)
    [IsProper p.left] [Surjective p.left] [IsProper P.hom]
    [IsSeparated (Z.hom ≫ Y.hom)] [LocallyOfFiniteType (Z.hom ≫ Y.hom)]
    [IsClosedImmersion (pullback.snd Z.hom p.left ≫ q.left)] :
    IsProper (Z.hom ≫ Y.hom) := by
  let ZS : Over S := Over.mk (Z.hom ≫ Y.hom)
  let WS : Over S := Over.mk (pullback.snd Z.hom p.left ≫ W.hom)
  let a : WS ⟶ ZS := Over.homMk (pullback.fst Z.hom p.left) (by
    dsimp only [ZS, WS, Over.mk_hom]
    rw [← Category.assoc, pullback.condition, Category.assoc, p.w])
  let b : WS ⟶ P := Over.homMk (pullback.snd Z.hom p.left ≫ q.left) (by
    dsimp only [WS, Over.mk_hom]
    rw [Category.assoc, q.w])
  have : IsProper b.left := inferInstanceAs
    (IsProper (pullback.snd Z.hom p.left ≫ q.left))
  have : IsProper WS.hom := isProper_hom_of_isProper_over_map b
  have : Surjective a.left := inferInstanceAs (Surjective (pullback.fst Z.hom p.left))
  have : IsSeparated ZS.hom := inferInstanceAs (IsSeparated (Z.hom ≫ Y.hom))
  have : LocallyOfFiniteType ZS.hom := inferInstanceAs (LocallyOfFiniteType (Z.hom ≫ Y.hom))
  exact isProper_of_surjective_over_proper a

end AlgebraicGeometry.Scheme.Approximation
