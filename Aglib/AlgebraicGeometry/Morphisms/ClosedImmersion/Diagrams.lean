/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Closed subschemes and limits of their defining ideals

A diagram of closed subschemes over a fixed scheme has the closed subscheme cut out by the
supremum of its ideals as its limit in the over category. For a connected indexing category,
the same cone is a limit in schemes. These statements concern the actual scheme structure,
not only the underlying intersection of closed sets.

The universal-property proofs are first established for arbitrary over diagrams and their
actual arrows. Only afterward are they specialized to the native ideal-sheaf subscheme
functor. This keeps the original limiting scheme and the original structural morphism.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ClosedSubscheme

variable {J : Type v} [Category.{w} J] {X Y : Scheme.{u}}

/-- A morphism whose kernel contains every diagram ideal gives its canonical cone.
The point is the original arrow `f`, not a chosen isomorphic closed subscheme. -/
def cone (F : J ⥤ Over Y) (f : X ⟶ Y)
    [∀ j, IsClosedImmersion (F.obj j).hom]
    (h : ∀ j, (F.obj j).hom.ker ≤ f.ker) : Cone F where
  pt := Over.mk f
  π :=
    { app j := Over.homMk (IsClosedImmersion.lift (F.obj j).hom f (h j))
      naturality i j a := by
        apply Over.OverMorphism.ext
        apply (cancel_mono (F.obj j).hom).1
        simp }

/-- The canonical projections retain the original structural map. -/
@[reassoc]
theorem cone_π_app_left_hom (F : J ⥤ Over Y) (f : X ⟶ Y)
    [∀ j, IsClosedImmersion (F.obj j).hom]
    (h : ∀ j, (F.obj j).hom.ker ≤ f.ker) (j : J) :
    ((cone F f h).π.app j).left ≫ (F.obj j).hom = f :=
  Over.w _

/-- Every projection from a closed subscheme into another closed subscheme is closed. -/
instance cone_projection_closed (F : J ⥤ Over Y) (f : X ⟶ Y) [IsClosedImmersion f]
    [∀ j, IsClosedImmersion (F.obj j).hom]
    (h : ∀ j, (F.obj j).hom.ker ≤ f.ker) (j : J) :
    IsClosedImmersion ((cone F f h).π.app j).left := by
  have : IsClosedImmersion (((cone F f h).π.app j).left ≫ (F.obj j).hom) := by
    rw [cone_π_app_left_hom]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (F.obj j).hom

/-- Ideal-theoretic equality gives the native universal property in the over category. -/
def isLimitCone (F : J ⥤ Over Y) (f : X ⟶ Y) [IsClosedImmersion f]
    [∀ j, IsClosedImmersion (F.obj j).hom]
    (h : ∀ j, (F.obj j).hom.ker ≤ f.ker)
    (hsup : (⨆ j, (F.obj j).hom.ker) = f.ker) : IsLimit (cone F f h) where
  lift s := Over.homMk (IsClosedImmersion.lift f s.pt.hom (by
    rw [← hsup]
    refine iSup_le fun j => ?_
    have hj := ((s.π.app j).left).le_ker_comp (F.obj j).hom
    rwa [Over.w] at hj)) (by
      change IsClosedImmersion.lift f s.pt.hom _ ≫ f = s.pt.hom
      exact IsClosedImmersion.lift_fac _ _ _)
  fac s j := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (F.obj j).hom).1
    simp [cone]
  uniq s m hm := by
    apply Over.OverMorphism.ext
    apply (cancel_mono f).1
    simpa only [cone, Over.mk_hom,
      Over.homMk_left, IsClosedImmersion.lift_fac] using Over.w m

/-- Forgetting the over structure retains the original limiting scheme and actual projections. -/
def schemeCone (F : J ⥤ Over Y) (f : X ⟶ Y)
    [∀ j, IsClosedImmersion (F.obj j).hom]
    (h : ∀ j, (F.obj j).hom.ker ≤ f.ker) : Cone (F ⋙ Over.forget Y) :=
  (Over.forget Y).mapCone (cone F f h)

/-- For a connected diagram, the original scheme is the limit in schemes themselves. -/
def isLimitSchemeCone [IsConnected J] (F : J ⥤ Over Y) (f : X ⟶ Y)
    [IsClosedImmersion f] [∀ j, IsClosedImmersion (F.obj j).hom]
    (h : ∀ j, (F.obj j).hom.ker ≤ f.ker)
    (hsup : (⨆ j, (F.obj j).hom.ker) = f.ker) : IsLimit (schemeCone F f h) :=
  isLimitOfPreserves (Over.forget Y) (isLimitCone F f h hsup)

/-- The native diagram of closed subschemes attached to a contravariant ideal diagram. -/
abbrev idealDiagram (D : J ⥤ Y.IdealSheafDataᵒᵖ) : J ⥤ Over Y :=
  D ⋙ Scheme.IdealSheafData.subschemeFunctor Y

instance idealDiagram_obj_closed (D : J ⥤ Y.IdealSheafDataᵒᵖ) (j : J) :
    IsClosedImmersion ((idealDiagram D).obj j).hom :=
  inferInstanceAs (IsClosedImmersion (D.obj j).unop.subschemeι)

/-- Every transition in a diagram of closed subschemes is a closed immersion. -/
instance diagram_map_closed (F : J ⥤ Over Y)
    [∀ j, IsClosedImmersion (F.obj j).hom] {i j : J} (a : i ⟶ j) :
    IsClosedImmersion (F.map a).left := by
  have : IsClosedImmersion ((F.map a).left ≫ (F.obj j).hom) := by
    rw [Over.w]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (F.obj j).hom

/-- An ideal supremum gives the canonical native cone on the original morphism. -/
def idealCone (D : J ⥤ Y.IdealSheafDataᵒᵖ) (f : X ⟶ Y)
    (hsup : (⨆ j, (D.obj j).unop) = f.ker) : Cone (idealDiagram D) :=
  cone (idealDiagram D) f (fun j => by
    change (D.obj j).unop.subschemeι.ker ≤ f.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, ← hsup]
    exact le_iSup (fun j => (D.obj j).unop) j)

/-- The ideal-supremum cone is limiting in the over category without a connectedness assumption. -/
def isLimitIdealCone (D : J ⥤ Y.IdealSheafDataᵒᵖ) (f : X ⟶ Y) [IsClosedImmersion f]
    (hsup : (⨆ j, (D.obj j).unop) = f.ker) : IsLimit (idealCone D f hsup) := by
  apply isLimitCone
  change (⨆ j, (D.obj j).unop.subschemeι.ker) = f.ker
  simpa only [Scheme.IdealSheafData.ker_subschemeι] using hsup

/-- The same original cone is limiting in schemes for every connected ideal diagram. -/
def isLimitIdealSchemeCone [IsConnected J] (D : J ⥤ Y.IdealSheafDataᵒᵖ)
    (f : X ⟶ Y) [IsClosedImmersion f]
    (hsup : (⨆ j, (D.obj j).unop) = f.ker) :
    IsLimit ((Over.forget Y).mapCone (idealCone D f hsup)) :=
  isLimitOfPreserves (Over.forget Y) (isLimitIdealCone D f hsup)

end AlgebraicGeometry.Scheme.ClosedSubscheme
