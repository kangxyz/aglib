/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered

/-!
# Limiting pullback cones from equifibered source diagrams

An equifibered diagram identifies each restriction of its source with the
native base-change diagram of its target. A limiting source cone whose
specified squares are cartesian therefore proves that the corresponding
native pullback cone is limiting. No limiting hypothesis on the target cone
is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace CategoryTheory.NatTrans.Equifibered

variable {I : Type w} [Category.{w'} I]
  {C : Type u} [Category.{v} C] [HasPullbacks C]
  {F G : I ⥤ C} (α : F ⟶ G) (hα : α.Equifibered)

/-- The original restricted source diagram is naturally isomorphic to the
literal pullbacks of the target diagram along one component. -/
def overPullbackIso (i : I) :
    Over.forget i ⋙ F ≅ Over.post G ⋙ Over.pullback (α.app i) ⋙ Over.forget (F.obj i) :=
  NatIso.ofComponents (fun k => (hα k.hom).flip.isoPullback) (by
    intro k l q
    apply pullback.hom_ext
    · simp [Over.post, Over.pullback_map_left, Category.assoc]
    · simp [Over.post, Over.pullback_map_left, Category.assoc, ← F.map_comp])

/-- An actual source cone with cartesian comparison squares identifies the
original pullback cone, including every native projection. -/
def overPullbackConeIso (cF : Cone F) (cG : Cone G) (a : cF.pt ⟶ cG.pt)
    (H : ∀ i, IsPullback (cF.π.app i) a (α.app i) (cG.π.app i)) (i : I) :
    (Cone.postcompose (overPullbackIso α hα i).hom).obj
        (cF.whisker (Over.forget i)) ≅
      (Over.pullback (α.app i) ⋙ Over.forget (F.obj i)).mapCone
        ((Over.conePost G i).obj cG) := by
  refine Cone.ext (H i).flip.isoPullback fun k => ?_
  apply pullback.hom_ext
  · simpa [overPullbackIso, Over.pullback_map_left, Category.assoc] using (H k.left).w
  · simp [overPullbackIso, Over.pullback_map_left, Category.assoc]

/-- A limiting source cone proves that the actual target cone pulled back
along any stage component is limiting. The target cone itself is not assumed
limiting. -/
def isLimitOverPullbackCone [IsCofiltered I]
    (cF : Cone F) (hcF : IsLimit cF) (cG : Cone G) (a : cF.pt ⟶ cG.pt)
    (H : ∀ i, IsPullback (cF.π.app i) a (α.app i) (cG.π.app i)) (i : I) :
    IsLimit ((Over.pullback (α.app i)).mapCone ((Over.conePost G i).obj cG)) := by
  letI : IsConnected (Over i) := IsCofiltered.isConnected (Over i)
  apply isLimitOfReflects (Over.forget (F.obj i))
  exact IsLimit.equivOfNatIsoOfIso (overPullbackIso α hα i) _ _
    (overPullbackConeIso α hα cF cG a H i)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) cF).symm hcF)

end CategoryTheory.NatTrans.Equifibered
