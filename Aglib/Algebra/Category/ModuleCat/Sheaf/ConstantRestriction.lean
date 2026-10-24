/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantLocalHom
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Constant module morphisms on actual site slices

The native constant sheaf restricts to the native constant sheaf on a slice.
The comparison is the map induced by restricting the original sheafification
unit. The local equations for a finitely presented module thus identify actual
restricted sheaf morphisms with constant module morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat.Sheaf

universe u v r

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type r} [Ring R]

attribute [local instance] hasSheafify

/-- The original constant-presheaf unit induces the map to the actual slice
restriction of the constant module sheaf. -/
def constantOverMap (U : C) (M : ModuleCat.{max u v} R) :
    (constantSheaf (J.over U) (ModuleCat.{max u v} R)).obj M ⟶
      (J.overPullback (ModuleCat.{max u v} R) U).obj
        ((constantSheaf J (ModuleCat.{max u v} R)).obj M) :=
  ((sheafificationAdjunction (J.over U) (ModuleCat.{max u v} R)).homEquiv _ _).symm
    (Functor.whiskerLeft (Over.forget U).op (constantUnit J M))

/-- The comparison retains the literal restricted sheafification unit. -/
theorem constantOverMap_unit (U : C) (M : ModuleCat.{max u v} R) :
    constantUnit (J.over U) M ≫ (constantOverMap J U M).hom =
      Functor.whiskerLeft (Over.forget U).op (constantUnit J M) := by
  exact toSheafify_sheafifyLift (J.over U) _ _

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to the actual slice commutes with native constant modules. -/
instance constantOverMap_isIso (U : C) (M : ModuleCat.{max u v} R) :
    IsIso (constantOverMap J U M) := by
  let : PreservesFilteredColimits (forget (ModuleCat.{max u v} R)) :=
    forget_preservesFilteredColimits R
  let : J.PreservesSheafification (forget (ModuleCat.{max u v} R)) :=
    GrothendieckTopology.instPreservesSheafification J (forget (ModuleCat.{max u v} R))
  let : (J.over U).PreservesSheafification (forget (ModuleCat.{max u v} R)) :=
    GrothendieckTopology.instPreservesSheafification (J.over U)
      (forget (ModuleCat.{max u v} R))
  let : CategoryTheory.Presheaf.IsLocallySurjective J (constantUnit J M) :=
    CategoryTheory.Presheaf.isLocallySurjective_toSheafify' J
      (D := ModuleCat.{max u v} R) ((Functor.const Cᵒᵖ).obj M)
  let : CategoryTheory.Presheaf.IsLocallyInjective J (constantUnit J M) :=
    CategoryTheory.Presheaf.isLocallyInjective_toSheafify' J
      (D := ModuleCat.{max u v} R) ((Functor.const Cᵒᵖ).obj M)
  let F := (J.overPullback (ModuleCat.{max u v} R) U).obj
    ((constantSheaf J (ModuleCat.{max u v} R)).obj M)
  let η : (Functor.const (Over U)ᵒᵖ).obj M ⟶ F.obj :=
    Functor.whiskerLeft (Over.forget U).op (constantUnit J M)
  let : CategoryTheory.Presheaf.IsLocallySurjective (J.over U) η :=
    CategoryTheory.Presheaf.isLocallySurjective_whisker
      (J.over U) J (Over.forget U) (constantUnit J M)
  let : CategoryTheory.Presheaf.IsLocallyInjective (J.over U) η :=
    CategoryTheory.Presheaf.isLocallyInjective_whisker
      (J.over U) J (Over.forget U) (constantUnit J M)
  have hη : (J.over U).W η := (J.over U).W_of_isLocallyBijective η
  let : IsIso ((presheafToSheaf (J.over U) (ModuleCat.{max u v} R)).map η) :=
    ((J.over U).W_iff η).mp hη
  change IsIso
    (((sheafificationAdjunction (J.over U) (ModuleCat.{max u v} R)).homEquiv _ F).symm η)
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The original unit-based map, as an isomorphism of module sheaves. -/
def constantOverIso (U : C) (M : ModuleCat.{max u v} R) :
    (constantSheaf (J.over U) (ModuleCat.{max u v} R)).obj M ≅
      (J.overPullback (ModuleCat.{max u v} R) U).obj
        ((constantSheaf J (ModuleCat.{max u v} R)).obj M) :=
  asIso (constantOverMap J U M)

set_option backward.isDefEq.respectTransparency false in
/-- A local constant-unit equation identifies the original morphism on the
entire actual slice, not just its value at one object. -/
theorem constantOverMap_naturality_of_unit
    {M N : ModuleCat.{max u v} R}
    (φ : (constantSheaf J (ModuleCat.{max u v} R)).obj M ⟶
      (constantSheaf J (ModuleCat.{max u v} R)).obj N)
    (U : C) (a : M ⟶ N)
    (ha : (constantUnit J M).app (op U) ≫ φ.hom.app (op U) =
      a ≫ (constantUnit J N).app (op U)) :
    constantOverMap J U M ≫ (J.overPullback (ModuleCat.{max u v} R) U).map φ =
      (constantSheaf (J.over U) (ModuleCat.{max u v} R)).map a ≫
        constantOverMap J U N := by
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext (J.over U) _ _
    ((J.overPullback (ModuleCat.{max u v} R) U).obj
      ((constantSheaf J (ModuleCat.{max u v} R)).obj N)).property
  change constantUnit (J.over U) M ≫
      (constantOverMap J U M).hom ≫
        ((J.overPullback (ModuleCat.{max u v} R) U).map φ).hom =
    constantUnit (J.over U) M ≫
      sheafifyMap (J.over U) ((Functor.const (Over U)ᵒᵖ).map a) ≫
        (constantOverMap J U N).hom
  rw [← Category.assoc, constantOverMap_unit, ← toSheafify_naturality_assoc,
    constantOverMap_unit]
  apply NatTrans.ext
  funext V
  exact constantUnit_hom_naturality J φ V.unop.hom a ha

end ModuleCat.Sheaf
