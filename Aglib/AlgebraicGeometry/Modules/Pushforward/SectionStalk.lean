/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/SectionPushforwardModuleStalk.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 81]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The scalar retraction from a genuine geometric section

A section equation identifies the scalar action obtained by restricting the
pushforward stalk along the original projection with the original module stalk
action. The sole point transport is the canonical stalk congruence.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry Topology

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- The point equality supplied by the actual section equation. -/
theorem section_stalk_point {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) (x : X) : p (i x) = x :=
  congrArg (fun f : X ⟶ X => f x) h

/-- The original projection stalk map after the canonical section point transport. -/
def sectionStalkRingMap {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) (x : X) : X.presheaf.stalk x ⟶ Y.presheaf.stalk (i x) :=
  (X.presheaf.stalkCongr (.of_eq (section_stalk_point i p h x))).inv ≫ p.stalkMap (i x)

/-- The original stalk maps form a ring retraction, including the necessary point transport. -/
theorem sectionStalkRingMap_retraction {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) (x : X) :
    sectionStalkRingMap i p h x ≫ i.stalkMap x = 𝟙 (X.presheaf.stalk x) := by
  unfold sectionStalkRingMap
  rw [Category.assoc, ← Scheme.Hom.stalkMap_comp,
    Scheme.Hom.stalkMap_congr_hom _ _ h x, Scheme.Hom.stalkMap_id]
  erw [Category.comp_id]
  exact Iso.inv_hom_id _

/-- Ring-hom form of the genuine section retraction. -/
theorem sectionStalkRingMap_hom_comp {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) (x : X) :
    (i.stalkMap x).hom.comp (sectionStalkRingMap i p h x).hom =
      RingHom.id (X.presheaf.stalk x) :=
  congrArg (fun f : X.presheaf.stalk x ⟶ X.presheaf.stalk x => f.hom)
    (sectionStalkRingMap_retraction i p h x)

/-- After restriction along the original projection, an embedded section's
pushforward stalk has precisely the original source module action. -/
def sectionPushforwardModuleStalkIso {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) (hi : IsInducing i) (x : X) :
    (Scheme.Modules.pushforward i ⋙ moduleStalk Y (i x)) ⋙
        ModuleCat.restrictScalars (sectionStalkRingMap i p h x).hom ≅ moduleStalk X x :=
  Functor.isoWhiskerRight (pushforwardModuleStalkIso i hi x)
      (ModuleCat.restrictScalars (sectionStalkRingMap i p h x).hom) ≪≫
    Functor.associator (moduleStalk X x) (ModuleCat.restrictScalars (i.stalkMap x).hom)
      (ModuleCat.restrictScalars (sectionStalkRingMap i p h x).hom) ≪≫
    Functor.isoWhiskerLeft (moduleStalk X x)
      ((ModuleCat.restrictScalarsComp' (sectionStalkRingMap i p h x).hom
        (i.stalkMap x).hom (RingHom.id (X.presheaf.stalk x))
        (sectionStalkRingMap_hom_comp i p h x).symm).symm ≪≫
        ModuleCat.restrictScalarsId' (RingHom.id (X.presheaf.stalk x)) rfl) ≪≫
    Functor.rightUnitor (moduleStalk X x)

/-- The section comparison still takes a germ to the same germ, without a sign or scalar twist. -/
theorem sectionPushforwardModuleStalkIso_germ {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X)
    (h : i ≫ p = 𝟙 X) (hi : IsInducing i) (x : X) (M : X.Modules)
    (U : Y.Opens) (hx : i x ∈ U) (s : Γ(M, i ⁻¹ᵁ U)) :
    (sectionPushforwardModuleStalkIso i p h hi x).hom.app M
      (((Scheme.Modules.pushforward i).obj M).presheaf.germ U (i x) hx s) =
      M.presheaf.germ (i ⁻¹ᵁ U) x hx s :=
  pushforwardModuleStalkMap_germ i x M U hx s

end AlgebraicGeometry.Scheme.Modules
