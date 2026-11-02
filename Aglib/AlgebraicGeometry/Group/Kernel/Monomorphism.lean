/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Mathlib.CategoryTheory.EpiMono

/-!
# The original scheme kernel of a monomorphism

Over any base, the structure map of the existing kernel is monic by its
original pullback square. Its original group unit is a section. Thus the
structure map itself is an isomorphism. The canonical comparison with the
base retains this map and identifies the inverse followed by the original
kernel inclusion with the original group unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.Kernel

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {G E : Grp (Over S)} (p : G ⟶ E)
  [Mono p.hom.hom.left]

set_option backward.isDefEq.respectTransparency false in
/-- The structure morphism of the original scheme kernel is itself an
isomorphism, without a reducedness, field or finiteness hypothesis. -/
instance isIso_structureMap_of_mono : IsIso (group p).X.hom := by
  have : Mono (group p).X.hom := (schemeSquare p).mono_snd_of_mono
  have : IsSplitEpi (group p).X.hom :=
    IsSplitEpi.mk' ⟨η[(group p).X].left, Over.w η[(group p).X]⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- The canonical isomorphism is the original kernel structure map. -/
def isoBaseOfMono : (group p).X.left ≅ S := asIso (group p).X.hom

@[simp]
theorem isoBaseOfMono_hom : (isoBaseOfMono p).hom = (group p).X.hom := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse is exactly the original unit of the existing kernel group. -/
theorem isoBaseOfMono_inv : (isoBaseOfMono p).inv = η[(group p).X].left := by
  apply (cancel_mono (group p).X.hom).mp
  rw [← isoBaseOfMono_hom p, Iso.inv_hom_id]
  exact (Over.w η[(group p).X]).symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse followed by the actual kernel inclusion is the
original unit section of G, as a whole scheme morphism. -/
@[reassoc (attr := simp)]
theorem isoBaseOfMono_inv_inclusion :
    (isoBaseOfMono p).inv ≫ (inclusion p).hom.hom.left = η[G.X].left := by
  rw [isoBaseOfMono_inv, ← Over.comp_left]
  exact congrArg Over.Hom.left (IsMonHom.one_hom (inclusion p).hom.hom)

/-- In particular the actual scheme kernel is finite over the original base. -/
theorem finite_of_mono : IsFinite (group p).X.hom := inferInstance

end AlgebraicGeometry.Scheme.Group.Kernel
