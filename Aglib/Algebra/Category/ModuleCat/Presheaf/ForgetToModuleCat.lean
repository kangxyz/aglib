/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Exact native module-presheaf sections over an initial ring

The original functor from module presheaves to presheaves over the ring at
an initial object is exact. Pointwise scalar forgetting gives literally the
original additive presheaf functor. It preserves finite limits and colimits
and reflects those limits and colimits, so exactness follows without any
commutativity, localization, sheaf or geometric hypothesis.

Ring, module and indexing-category universes are independent.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace PresheafOfModules

universe r m c h

variable {C : Type c} [Category.{h} C] {R : Cᵒᵖ ⥤ RingCat.{r}}
  (X : Cᵒᵖ) (hX : IsInitial X)

/-- Forgetting the initial-ring action gives the unchanged original additive presheaf. -/
def forgetToPresheafModuleCatCompForgetIso :
    forgetToPresheafModuleCat.{m} X hX ⋙
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{m} (R.obj X)) AddCommGrpCat.{m}).obj
        (forget₂ (ModuleCat.{m} (R.obj X)) AddCommGrpCat.{m}) ≅ toPresheaf.{m} R :=
  Iso.refl _

instance forgetToPresheafModuleCat_additive :
    (forgetToPresheafModuleCat.{m} (R := R) X hX).Additive where
  map_add := by intros; ext U x; rfl

instance forgetToPresheafModuleCat_preservesFiniteLimits :
    PreservesFiniteLimits (forgetToPresheafModuleCat.{m} (R := R) X hX) := by
  let F := forgetToPresheafModuleCat.{m} (R := R) X hX
  let G := (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{m} (R.obj X)) AddCommGrpCat.{m}).obj
    (forget₂ (ModuleCat.{m} (R.obj X)) AddCommGrpCat.{m})
  let : HasFiniteLimits (Cᵒᵖ ⥤ ModuleCat.{m} (R.obj X)) := ⟨fun _ ↦ inferInstance⟩
  let : PreservesFiniteLimits G := ⟨fun _ ↦ inferInstance⟩
  let : ReflectsFiniteLimits G := reflectsFiniteLimits_of_reflectsIsomorphisms G
  let : PreservesFiniteLimits (F ⋙ G) :=
    preservesFiniteLimits_of_natIso (forgetToPresheafModuleCatCompForgetIso X hX).symm
  exact preservesFiniteLimits_of_reflects_of_preserves F G

instance forgetToPresheafModuleCat_preservesFiniteColimits :
    PreservesFiniteColimits (forgetToPresheafModuleCat.{m} (R := R) X hX) := by
  let F := forgetToPresheafModuleCat.{m} (R := R) X hX
  let G := (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{m} (R.obj X)) AddCommGrpCat.{m}).obj
    (forget₂ (ModuleCat.{m} (R.obj X)) AddCommGrpCat.{m})
  let : HasFiniteColimits (Cᵒᵖ ⥤ ModuleCat.{m} (R.obj X)) := ⟨fun _ ↦ inferInstance⟩
  let : PreservesFiniteColimits G := ⟨fun _ ↦ inferInstance⟩
  let : ReflectsFiniteColimits G := reflectsFiniteColimitsOfReflectsIsomorphisms G
  let : PreservesFiniteColimits (F ⋙ G) :=
    preservesFiniteColimits_of_natIso (forgetToPresheafModuleCatCompForgetIso X hX).symm
  exact preservesFiniteColimits_of_reflects_of_preserves F G

instance forgetToPresheafModuleCat_preservesHomology :
    (forgetToPresheafModuleCat.{m} (R := R) X hX).PreservesHomology := by infer_instance

end PresheafOfModules
