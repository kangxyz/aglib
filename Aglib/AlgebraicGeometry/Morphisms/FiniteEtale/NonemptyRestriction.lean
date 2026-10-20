/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.ConnectedRigidity
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Restriction of connected finite-etale covers to a nonempty pullback

The actual base-change functor is injective on morphisms out of a connected
cover when that cover's literal pullback is nonempty. The existing clopen
equalizer theorem proves equality of the original scheme morphisms, so the
same restriction retains the exact order of every deck automorphism.

Source: selected declarations at lines 28–68 of
`R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.NonemptyRestriction`,
R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9ab5abf61e921d613603e7569361278bb81a6c0cf56af3bf575b50ab9a2dd26e`.
The native `Scheme.Hom.eq_of_comp_eq_of_nonempty` is reused directly. No
faithfulness, density, Noetherianity or comparison-equivalence premise is added.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The actual pullback of a cover morphism commutes with projection to the
original covering scheme. -/
@[reassoc] theorem baseChange_map_left_fst {X S : Scheme.{u}}
    (s : S ⟶ X) {C D : Scheme.FiniteEtale X} (f : C ⟶ D) :
    ((baseChange s).map f).hom.left ≫ pullback.fst D.obj.hom s =
      pullback.fst C.obj.hom s ≫ f.hom.left :=
  pullback.lift_fst _ _ _

/-- Restriction of morphisms from a connected finite-etale cover is injective
whenever its actual pullback is nonempty. No assumed faithfulness or generic
density is needed. -/
theorem baseChange_map_injective_of_connected {X S : Scheme.{u}}
    (s : S ⟶ X) (C D : Scheme.FiniteEtale X) [ConnectedSpace C.obj.left]
    [Nonempty ((baseChange s).obj C).obj.left] :
    Function.Injective (fun f : C ⟶ D => (baseChange s).map f) := by
  let : Nonempty (pullback C.obj.hom s : Scheme.{u}) :=
    inferInstanceAs (Nonempty ((baseChange s).obj C).obj.left)
  intro f g h
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply Scheme.Hom.eq_of_comp_eq_of_nonempty D.obj.hom
    (pullback.fst C.obj.hom s) f.hom.left g.hom.left
  · exact (Over.w f.hom).trans (Over.w g.hom).symm
  · have hh := congrArg (fun q => q.hom.left ≫ pullback.fst D.obj.hom s) h
    simpa only [baseChange_map_left_fst] using hh

/-- Hence actual deck automorphisms retain their exact order under that
nonempty base change. -/
theorem baseChange_mapAut_injective_of_connected {X S : Scheme.{u}}
    (s : S ⟶ X) (C : Scheme.FiniteEtale X) [ConnectedSpace C.obj.left]
    [Nonempty ((baseChange s).obj C).obj.left] :
    Function.Injective ((baseChange s).mapAut C) := by
  intro f g h
  apply Aut.ext
  exact baseChange_map_injective_of_connected s C C (congrArg Iso.hom h)

theorem baseChange_mapAut_orderOf {X S : Scheme.{u}}
    (s : S ⟶ X) (C : Scheme.FiniteEtale X) [ConnectedSpace C.obj.left]
    [Nonempty ((baseChange s).obj C).obj.left] (g : Aut C) :
    orderOf ((baseChange s).mapAut C g) = orderOf g :=
  orderOf_injective _ (baseChange_mapAut_injective_of_connected s C) g

end AlgebraicGeometry.Scheme.FiniteEtale
