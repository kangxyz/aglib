/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PointSupportedSubobject
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.Data.Finset.Lattice.Fold

/-! # The actual filtered diagram of finite closed support subobjects -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Set

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u})

/-- Finite sets of closed points, lifted only to the native coefficient-colimit index universe. -/
abbrev FiniteSupportIndex := Finset (ULift.{u + 1} {x : X // IsClosed ({x} : Set X)})

/-- The actual finite subset of the underlying scheme belonging to a support stage. -/
def finiteSupportSet (Z : FiniteSupportIndex X) : Set X :=
  (fun z => z.down.val) '' (Z : Set (ULift.{u + 1} {x : X // IsClosed ({x} : Set X)}))

theorem finiteSupportSet_finite (Z : FiniteSupportIndex X) : (finiteSupportSet X Z).Finite :=
  Z.finite_toSet.image _

theorem finiteSupportSet_closed_points (Z : FiniteSupportIndex X) (x : X)
    (hx : x ∈ finiteSupportSet X Z) : IsClosed ({x} : Set X) := by
  obtain ⟨z, _, rfl⟩ := hx
  exact z.down.property

theorem finiteSupportSet_closed (Z : FiniteSupportIndex X) : IsClosed (finiteSupportSet X Z) :=
by
  simpa only [Set.biUnion_of_singleton] using
    (finiteSupportSet_finite X Z).isClosed_biUnion (finiteSupportSet_closed_points X Z)

theorem finiteSupportSet_mono : Monotone (finiteSupportSet X) := by
  intro Z W h
  exact Set.image_mono h

variable {X} (F : AbelianSheaf.{u, u + 1} X)

/-- The order functor of original finite closed support subobjects. -/
def finiteSupportSubobjects : FiniteSupportIndex X ⥤ Subobject F :=
  (show Monotone (fun Z => pointSupportedSubobject F (finiteSupportSet X Z)) from
    fun _ _ h => pointSupportedSubobject_mono F (finiteSupportSet_mono X h)).functor

/-- The same diagram retaining each actual inclusion into the original coefficient. -/
def finiteSupportMonoOver : FiniteSupportIndex X ⥤ MonoOver F :=
  finiteSupportSubobjects F ⋙ Subobject.representative

/-- The actual coefficient diagram, not a replacement by chosen stalk groups. -/
def finiteSupportDiagram : FiniteSupportIndex X ⥤ AbelianSheaf.{u, u + 1} X :=
  finiteSupportMonoOver F ⋙ MonoOver.forget F ⋙ Over.forget F

/-- The canonical cocone consists of the original supported-subobject inclusions. -/
def finiteSupportCocone : Cocone (finiteSupportDiagram F) where
  pt := F
  ι := {
    app Z := (pointSupportedSubobject F (finiteSupportSet X Z)).arrow
    naturality Z W f := by
      exact MonoOver.w ((finiteSupportMonoOver F).map f) }

/-- The map from the actual filtered coefficient colimit to the original sheaf. -/
def finiteSupportColimitMap : colimit (finiteSupportDiagram F) ⟶ F :=
  colimit.desc _ (finiteSupportCocone F)

@[reassoc (attr := simp)]
theorem finiteSupportColimitMap_ι (Z : FiniteSupportIndex X) :
    colimit.ι (finiteSupportDiagram F) Z ≫ finiteSupportColimitMap F =
      (pointSupportedSubobject F (finiteSupportSet X Z)).arrow :=
  colimit.ι_desc _ _

/-- Filtered exactness makes the actual exhaustion map monic, without any claim that
geometric stalks preserve an infinite intersection of support conditions. -/
theorem finiteSupportColimitMap_mono : Mono (finiteSupportColimitMap F) := by
  apply IsGrothendieckAbelian.mono_of_isColimit_monoOver
    (finiteSupportMonoOver F) (colimit.isColimit (finiteSupportDiagram F))
    (finiteSupportColimitMap F)
  intro Z
  exact finiteSupportColimitMap_ι F Z

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
