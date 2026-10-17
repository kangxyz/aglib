/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Picard presheaves on schemes over a base

For a morphism of schemes `p : X ⟶ S`, this file constructs presheaves of
additive commutative groups on `Over S`. All values are the actual Picard groups
`PicardGroup` of isomorphism classes of line bundles, and all maps are the
proved additive pullback `PullbackTensor.Local.pullbackHom`.

* `picardFunctor` is `Y ↦ Pic(Y)` on all schemes.
* `basePicardFunctor S` is `T ↦ Pic(T)` on `Over S`.
* `familyScheme p` is the base-change family `T ↦ X ×_S T`, with the canonical
  maps `pullback.map` between fibre products, and `familyProjection p` is the
  second projection `X ×_S T ⟶ T`.
* `familyPicardFunctor p` is `T ↦ Pic(X ×_S T)`, Kleiman's absolute Picard
  functor `Pic_X` (Kleiman, *The Picard scheme*, arXiv:math/0504020v1,
  Def. 2.1, p. 16).
* `basePullback p` is pullback along the projections `X ×_S T ⟶ T`.
* `relativePicardFunctor p` is the relative Picard functor
  `P_{X/S}(T) = Pic(X ×_S T) / Pic(T)` (Kleiman, Def. 2.2, p. 17), with its
  quotient map `quotientProjection p`.

The functors are defined on all of `Over S`; nonreduced and non-Noetherian test
schemes are included. Kleiman defines these functors on locally Noetherian
`S`-schemes; the functors here restrict to his on that full subcategory. Values lie
in `AddCommGrpCat.{u + 1}` because `PicardGroup T` is a quotient of objects of
`SheafOfModules.{u}`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local

universe u

/-- The Picard presheaf `Y ↦ Pic(Y)` on all schemes, with the additive pullback of
line-bundle classes as restriction maps. -/
def picardFunctor : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj Y := AddCommGrpCat.of (PicardGroup Y.unop)
  map f := AddCommGrpCat.ofHom (pullbackHom f.unop)
  map_id Y := by
    ext a
    exact pullbackClass_id a
  map_comp f g := by
    ext a
    exact pullbackClass_comp g.unop f.unop a

theorem picardFunctor_obj (Y : Scheme.{u}ᵒᵖ) :
    picardFunctor.obj Y = AddCommGrpCat.of (PicardGroup Y.unop) := rfl

@[simp]
theorem picardFunctor_map {Y Z : Scheme.{u}ᵒᵖ} (f : Y ⟶ Z) :
    picardFunctor.map f = AddCommGrpCat.ofHom (pullbackHom f.unop) := rfl

theorem picardFunctor_map_apply {Y Z : Scheme.{u}ᵒᵖ} (f : Y ⟶ Z) (a : PicardGroup Y.unop) :
    (picardFunctor.map f).hom a = pullbackClass f.unop a := rfl

variable {S X : Scheme.{u}}

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
/-- The base-change family `T ↦ X ×_S T` on `Over S`. A morphism `f : T ⟶ T'` of
`S`-schemes induces the canonical map `pullback.map` of fibre products. -/
@[simps obj]
def familyScheme (p : X ⟶ S) : Over S ⥤ Scheme.{u} where
  obj T := pullback p T.hom
  map {T T'} f := pullback.map p T.hom p T'.hom (𝟙 X) f.left (𝟙 S) (by simp) (by simp)
  map_id T := by
    apply pullback.hom_ext <;> simp [pullback.map]
  map_comp f g := by
    apply pullback.hom_ext <;> simp [pullback.map]

theorem familyScheme_map (p : X ⟶ S) {T T' : Over S} (f : T ⟶ T') :
    (familyScheme p).map f =
      pullback.map p T.hom p T'.hom (𝟙 X) f.left (𝟙 S) (by simp) (by simp) := rfl

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem familyScheme_map_fst (p : X ⟶ S) {T T' : Over S} (f : T ⟶ T') :
    (familyScheme p).map f ≫ pullback.fst p T'.hom = pullback.fst p T.hom := by
  simp [familyScheme_map, pullback.map]

-- `pullback.map` is a `pullback.lift` carrying its own `HasPullback` instances; relaxing
-- instance transparency lets `pullback.lift_fst`/`pullback.lift_snd` match them, as in
-- Mathlib's `pullback.map_comp` and `pullback.map_id`.
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem familyScheme_map_snd (p : X ⟶ S) {T T' : Over S} (f : T ⟶ T') :
    (familyScheme p).map f ≫ pullback.snd p T'.hom = pullback.snd p T.hom ≫ f.left := by
  simp [familyScheme_map, pullback.map]

/-- The projection `X ×_S T ⟶ T`, natural in the `S`-scheme `T`. -/
@[simps]
def familyProjection (p : X ⟶ S) : familyScheme p ⟶ Over.forget S where
  app T := pullback.snd p T.hom
  naturality T T' f := by
    rw [familyScheme_map_snd]
    rfl

/-- The base Picard presheaf `T ↦ Pic(T)` on `Over S`. -/
def basePicardFunctor (S : Scheme.{u}) : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (Over.forget S).op ⋙ picardFunctor

/-- The family Picard presheaf `T ↦ Pic(X ×_S T)` on `Over S`; this is Kleiman's
absolute Picard functor `Pic_X` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Def. 2.1, p. 16). -/
def familyPicardFunctor (p : X ⟶ S) : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (familyScheme p).op ⋙ picardFunctor

theorem basePicardFunctor_obj (T : (Over S)ᵒᵖ) :
    (basePicardFunctor S).obj T = AddCommGrpCat.of (PicardGroup T.unop.left) := rfl

theorem basePicardFunctor_map_apply {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (a : PicardGroup T.unop.left) :
    ((basePicardFunctor S).map f).hom a = pullbackClass f.unop.left a := rfl

theorem familyPicardFunctor_obj (p : X ⟶ S) (T : (Over S)ᵒᵖ) :
    (familyPicardFunctor p).obj T =
      AddCommGrpCat.of (PicardGroup (pullback p T.unop.hom)) := rfl

theorem familyPicardFunctor_map_apply (p : X ⟶ S) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (a : PicardGroup (pullback p T.unop.hom)) :
    ((familyPicardFunctor p).map f).hom a = pullbackClass ((familyScheme p).map f.unop) a :=
  rfl

/-- Pullback of line-bundle classes along the projections `X ×_S T ⟶ T`. -/
def basePullback (p : X ⟶ S) : basePicardFunctor S ⟶ familyPicardFunctor p :=
  Functor.whiskerRight (NatTrans.op (familyProjection p)) picardFunctor

theorem basePullback_app_apply (p : X ⟶ S) (T : (Over S)ᵒᵖ) (a : PicardGroup T.unop.left) :
    ((basePullback p).app T).hom a = pullbackClass (pullback.snd p T.unop.hom) a := rfl

/-- The image of `Pic(T)` in `Pic(X ×_S T)` under the base pullback. -/
abbrev baseImage (p : X ⟶ S) (T : (Over S)ᵒᵖ) : AddSubgroup ((familyPicardFunctor p).obj T) :=
  ((basePullback p).app T).hom.range

theorem baseImage_le_comap (p : X ⟶ S) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    baseImage p T ≤ (baseImage p T').comap ((familyPicardFunctor p).map f).hom := by
  rintro _ ⟨a, rfl⟩
  exact ⟨((basePicardFunctor S).map f).hom a,
    congrArg (fun φ => φ.hom a) ((basePullback p).naturality f)⟩

/-- The relative Picard functor `P_{X/S}(T) = Pic(X ×_S T) / Pic(T)`
(Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Def. 2.2, p. 17). The quotient
is by the image of the base pullback; no section and no hypothesis on `p` is
used. -/
def relativePicardFunctor (p : X ⟶ S) : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj T := AddCommGrpCat.of ((familyPicardFunctor p).obj T ⧸ baseImage p T)
  map f := AddCommGrpCat.ofHom
    (QuotientAddGroup.map _ _ ((familyPicardFunctor p).map f).hom (baseImage_le_comap p f))
  map_id T := by
    ext a
    change (QuotientAddGroup.mk (((familyPicardFunctor p).map (𝟙 T)).hom a) :
      (familyPicardFunctor p).obj T ⧸ baseImage p T) = QuotientAddGroup.mk a
    rw [(familyPicardFunctor p).map_id]
    rfl
  map_comp {T T' T''} f g := by
    ext a
    change (QuotientAddGroup.mk (((familyPicardFunctor p).map (f ≫ g)).hom a) :
      (familyPicardFunctor p).obj T'' ⧸ baseImage p T'') =
        QuotientAddGroup.mk (((familyPicardFunctor p).map g).hom
          (((familyPicardFunctor p).map f).hom a))
    rw [(familyPicardFunctor p).map_comp]
    rfl

theorem relativePicardFunctor_obj (p : X ⟶ S) (T : (Over S)ᵒᵖ) :
    (relativePicardFunctor p).obj T =
      AddCommGrpCat.of ((familyPicardFunctor p).obj T ⧸ baseImage p T) := rfl

theorem relativePicardFunctor_map_mk (p : X ⟶ S) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (a : (familyPicardFunctor p).obj T) :
    ((relativePicardFunctor p).map f).hom (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (((familyPicardFunctor p).map f).hom a) := rfl

/-- The quotient map `Pic(X ×_S T) ⟶ P_{X/S}(T)`, natural in `T`. -/
def quotientProjection (p : X ⟶ S) : familyPicardFunctor p ⟶ relativePicardFunctor p where
  app T := AddCommGrpCat.ofHom (QuotientAddGroup.mk' (baseImage p T))
  naturality T T' f := by
    ext a
    rfl

theorem quotientProjection_app_apply (p : X ⟶ S) (T : (Over S)ᵒᵖ)
    (a : (familyPicardFunctor p).obj T) :
    ((quotientProjection p).app T).hom a = QuotientAddGroup.mk a := rfl

theorem quotientProjection_app_surjective (p : X ⟶ S) (T : (Over S)ᵒᵖ) :
    Function.Surjective ((quotientProjection p).app T).hom :=
  QuotientAddGroup.mk'_surjective _

/-- The kernel of `Pic(X ×_S T) ⟶ P_{X/S}(T)` is the image of `Pic(T)`. -/
theorem quotientProjection_app_ker (p : X ⟶ S) (T : (Over S)ᵒᵖ) :
    ((quotientProjection p).app T).hom.ker = baseImage p T :=
  QuotientAddGroup.ker_mk' _

/-- The base pullback composed with the quotient map is zero. -/
@[simp]
theorem quotientProjection_basePullback_apply (p : X ⟶ S) (T : (Over S)ᵒᵖ)
    (a : PicardGroup T.unop.left) :
    ((quotientProjection p).app T).hom (((basePullback p).app T).hom a) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr ⟨a, rfl⟩

end AlgebraicGeometry.Scheme.RelativePicard
