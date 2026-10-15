/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Aglib.AlgebraicGeometry.Modules.Pushforward.SectionStalk

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/SectionPullbackStalk.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 41]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Pullback stalk at the point of a genuine section
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry Topology

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Canonical point transport for the actual pullback/module stalk comparison. -/
def pullbackModuleStalkAtEqIso {X Y : Scheme.{u}} (p : Y ⟶ X) (y : Y) (x : X)
    (hx : p y = x) :
    Scheme.Modules.pullback p ⋙ moduleStalk Y y ≅
      moduleStalk X x ⋙ ModuleCat.extendScalars
        (((X.presheaf.stalkCongr (.of_eq hx)).inv ≫ p.stalkMap y).hom) := by
  subst x
  simpa only [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp] using pullbackModuleStalkIso p y

/-- At a genuine section, the actual pullback stalk extends along the actual
projection stalk map. -/
def sectionPullbackModuleStalkIso {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) (x : X) :
    Scheme.Modules.pullback p ⋙ moduleStalk Y (i x) ≅
      moduleStalk X x ⋙ ModuleCat.extendScalars (sectionStalkRingMap i p h x).hom :=
  pullbackModuleStalkAtEqIso p (i x) x (section_stalk_point i p h x)

end AlgebraicGeometry.Scheme.Modules
