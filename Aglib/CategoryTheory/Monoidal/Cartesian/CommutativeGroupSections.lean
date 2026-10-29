/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.AdjunctionHomMulEquiv
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Additive sections of a commutative group object

The native Hom group of a commutative group object, written additively and
lifted once, gives a presheaf of abelian groups. Its restrictions and coefficient
maps are the native group-object Yoneda maps. The actual Hom equivalence of a
monoidal right adjoint gives the section comparison, with its original unit,
counit and naturality.

Consumers are represented coefficients on the small étale site and their
section functors on arbitrary relative schemes.
-/

@[expose] public section

open Opposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.CommutativeGroupSections

universe w v u u'

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

/-- Native sections, with additive spelling and one value-universe lift. -/
@[nolint unusedArguments]
abbrev Sections (H : Grp C) [IsCommMonObj H.X] (U : C) :=
  ULift.{w} (Additive (U ⟶ H.X))

/-- Precomposition is the lifted additive spelling of the native Yoneda map. -/
def pullback (H : Grp C) [IsCommMonObj H.X] {U V : C} (f : U ⟶ V) :
    Sections.{w} H V →+ Sections.{w} H U :=
  AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((((yonedaGrp.obj H).map f.op).hom.toAdditive).comp AddEquiv.ulift.toAddMonoidHom)

@[simp]
theorem pullback_apply (H : Grp C) [IsCommMonObj H.X] {U V : C} (f : U ⟶ V)
    (s : Sections.{w} H V) :
    pullback.{w} H f s = ULift.up (Additive.ofMul (f ≫ s.down.toMul)) := rfl

/-- The additive section functor retains the original objects and restrictions. -/
def functor (H : Grp C) [IsCommMonObj H.X] : Cᵒᵖ ⥤ AddCommGrpCat.{max v w} where
  obj U := AddCommGrpCat.of (Sections.{w} H U.unop)
  map f := AddCommGrpCat.ofHom (pullback.{w} H f.unop)
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ULift.ext
    exact congrArg Additive.ofMul (Category.id_comp s.down.toMul)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ULift.ext
    exact congrArg Additive.ofMul (Category.assoc g.unop f.unop s.down.toMul)

@[simp]
theorem functor_map_apply (H : Grp C) [IsCommMonObj H.X] {U V : Cᵒᵖ} (f : U ⟶ V)
    (s : Sections.{w} H U.unop) :
    (functor.{w} H).map f s = ULift.up (Additive.ofMul (f.unop ≫ s.down.toMul)) := rfl

/-- Forgetting addition gives the same Yoneda presheaf with the same one lift. -/
def forgetIso (H : Grp C) [IsCommMonObj H.X] :
    functor.{w} H ⋙ CategoryTheory.forget AddCommGrpCat.{max v w} ≅
      yoneda.obj H.X ⋙ uliftFunctor.{w} :=
  NatIso.ofComponents (fun U => Equiv.toIso {
    toFun := fun s => ULift.up s.down.toMul
    invFun := fun s => ULift.up (Additive.ofMul s.down)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl })
    (fun f => by ext s; rfl)

/-- Postcomposition is the lifted additive spelling of the native Yoneda map. -/
def postcompose {H K : Grp C} [IsCommMonObj H.X] [IsCommMonObj K.X]
    (q : H ⟶ K) (U : C) : Sections.{w} H U →+ Sections.{w} K U :=
  AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((((yonedaGrp.map q).app (op U)).hom.toAdditive).comp AddEquiv.ulift.toAddMonoidHom)

@[simp]
theorem postcompose_apply {H K : Grp C} [IsCommMonObj H.X] [IsCommMonObj K.X]
    (q : H ⟶ K) (U : C) (s : Sections.{w} H U) :
    postcompose.{w} q U s = ULift.up (Additive.ofMul (s.down.toMul ≫ q.hom.hom)) := rfl

/-- A map of group objects induces its original postcomposition on sections. -/
def map {H K : Grp C} [IsCommMonObj H.X] [IsCommMonObj K.X]
    (q : H ⟶ K) : functor.{w} H ⟶ functor.{w} K where
  app U := AddCommGrpCat.ofHom (postcompose.{w} q U.unop)
  naturality {U V} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ULift.ext
    exact congrArg Additive.ofMul (Category.assoc f.unop s.down.toMul q.hom.hom)

@[simp]
theorem map_id (H : Grp C) [IsCommMonObj H.X] :
    map.{w} (𝟙 H) = 𝟙 (functor.{w} H) := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ULift.ext
  exact congrArg Additive.ofMul (Category.comp_id s.down.toMul)

@[simp]
theorem map_comp {H K L : Grp C}
    [IsCommMonObj H.X] [IsCommMonObj K.X] [IsCommMonObj L.X]
    (q : H ⟶ K) (r : K ⟶ L) :
    map.{w} (q ≫ r) = map.{w} q ≫ map.{w} r := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ULift.ext
  exact congrArg Additive.ofMul (Category.assoc s.down.toMul q.hom.hom r.hom.hom).symm

/-- An actual group-object isomorphism acts through the native Yoneda `mapIso`. -/
def postcomposeEquiv {H K : Grp C} [IsCommMonObj H.X] [IsCommMonObj K.X]
    (e : H ≅ K) (U : C) : Sections.{w} H U ≃+ Sections.{w} K U :=
  (AddEquiv.ulift.trans
    (((yonedaGrp.mapIso e).app (op U)).groupIsoToMulEquiv).toAdditive).trans
      AddEquiv.ulift.symm

@[simp]
theorem postcomposeEquiv_apply {H K : Grp C} [IsCommMonObj H.X] [IsCommMonObj K.X]
    (e : H ≅ K) (U : C) (s : Sections.{w} H U) :
    postcomposeEquiv.{w} e U s = ULift.up (Additive.ofMul (s.down.toMul ≫ e.hom.hom.hom)) := rfl

@[simp]
theorem postcomposeEquiv_symm_apply {H K : Grp C}
    [IsCommMonObj H.X] [IsCommMonObj K.X]
    (e : H ≅ K) (U : C) (s : Sections.{w} K U) :
    (postcomposeEquiv.{w} e U).symm s =
      ULift.up (Additive.ofMul (s.down.toMul ≫ e.inv.hom.hom)) := rfl

/-- Postcomposition by the same group-object isomorphism is natural in all tests. -/
def mapIso {H K : Grp C} [IsCommMonObj H.X] [IsCommMonObj K.X]
    (e : H ≅ K) : functor.{w} H ≅ functor.{w} K :=
  NatIso.ofComponents
    (fun U => AddEquiv.toAddCommGrpIso (postcomposeEquiv.{w} e U.unop)) (by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ULift.ext
    exact congrArg Additive.ofMul (Category.assoc f.unop s.down.toMul e.hom.hom.hom))

section Adjunction

open scoped CategoryTheory.Obj

variable {D : Type u'} [Category.{v} D] [CartesianMonoidalCategory D] [BraidedCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Monoidal]
  (H : Grp D) [IsCommMonObj H.X] [IsCommMonObj (R.mapGrp.obj H).X]

/-- The actual adjunction Hom equivalence, written additively and lifted once. -/
def adjunctionEquiv (U : C) :
    Sections.{w} H (L.obj U) ≃+ Sections.{w} (R.mapGrp.obj H) U :=
  (AddEquiv.ulift.trans (adj.homMulEquiv (M := H.X) U).toAdditive).trans
    AddEquiv.ulift.symm

@[simp]
theorem adjunctionEquiv_apply (U : C) (s : Sections.{w} H (L.obj U)) :
    adjunctionEquiv.{w} adj H U s =
      ULift.up (Additive.ofMul (adj.homEquiv U H.X s.down.toMul)) := rfl

@[simp]
theorem adjunctionEquiv_symm_apply (U : C) (s : Sections.{w} (R.mapGrp.obj H) U) :
    (adjunctionEquiv.{w} adj H U).symm s =
      ULift.up (Additive.ofMul ((adj.homEquiv U H.X).symm s.down.toMul)) := rfl

/-- The section comparison retains the actual unit of the given adjunction. -/
theorem adjunctionEquiv_unit (U : C) (s : Sections.{w} H (L.obj U)) :
    adjunctionEquiv.{w} adj H U s =
      ULift.up (Additive.ofMul (adj.unit.app U ≫ R.map s.down.toMul)) := rfl

/-- Its inverse retains the actual counit of the same adjunction. -/
theorem adjunctionEquiv_symm_counit (U : C) (s : Sections.{w} (R.mapGrp.obj H) U) :
    (adjunctionEquiv.{w} adj H U).symm s =
      ULift.up (Additive.ofMul (L.map s.down.toMul ≫ adj.counit.app H.X)) := rfl

/-- Hom-equivalence naturality supplies the whole additive section comparison. -/
def adjunctionIso :
    L.op ⋙ functor.{w} H ≅ functor.{w} (R.mapGrp.obj H) :=
  NatIso.ofComponents (fun U => AddEquiv.toAddCommGrpIso (adjunctionEquiv.{w} adj H U.unop)) (by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply ULift.ext
    exact congrArg Additive.ofMul
      (adj.homEquiv_naturality_left f.unop s.down.toMul))

end Adjunction

/-- An actual identity-power equation annihilates every original lifted additive section. -/
theorem sections_nsmul_eq_zero_of_identity_pow
    (H : Grp C) [IsCommMonObj H.X] (n : ℕ)
    (h : (𝟙 H.X : H.X ⟶ H.X) ^ n = 1) (U : C) (t : Sections.{w} H U) :
    n • t = 0 := by
  apply ULift.ext
  change Additive.ofMul (t.down.toMul ^ n) = Additive.ofMul 1
  apply congrArg Additive.ofMul
  calc
    t.down.toMul ^ n = t.down.toMul ≫ (𝟙 H.X : H.X ⟶ H.X) ^ n := by
      rw [MonObj.comp_pow, Category.comp_id]
    _ = 1 := by rw [h, MonObj.comp_one]

end CategoryTheory.CommutativeGroupSections
