/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TorsorAction

/-!
# Lifting actual finite-etale group maps through fully faithful pullback

Fullness and faithfulness of the displayed finite-etale pullback
construct actual group-scheme morphisms and isomorphisms. The pullback
equations refer to those chosen maps, with the original finite-etale premises.

Source: `R5Lab.Aglib.AlgebraicGeometry.Group.BaseChange.FullFaithful`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`6cc872fee4d63ecd6b0adac1742e51e1cf2e2d26efa6df80aa606caed7975589`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.PreGaloisCategory CategoryTheory.Obj
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.GroupDescent
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
attribute [local instance] Over.braidedCategory coverCartesian

namespace AlgebraicGeometry.Scheme.Group.BaseChange

universe u
attribute [local instance] Over.cartesianMonoidalCategory

section GroupExtension
variable {X Z : Scheme.{u}} (j : Z ⟶ X)
  [(baseChange j).Full] [(baseChange j).Faithful]

omit [(baseChange j).Full] [(baseChange j).Faithful] in
theorem finite_pullback_map_ext [(baseChange j).Full] [(baseChange j).Faithful]
    (Y W : Scheme.FiniteEtale X) {f g : Y.obj ⟶ W.obj}
    (h : (Over.pullback j).map f = (Over.pullback j).map g) : f = g := by
  have hc : (baseChange j).map (ObjectProperty.homMk f) =
      (baseChange j).map (ObjectProperty.homMk g) := by
    apply ObjectProperty.hom_ext
    exact h
  exact congrArg (fun q => q.hom) ((baseChange j).map_injective hc)

variable (H J : Grp (Over X))
  [IsFinite H.X.hom] [Etale H.X.hom] [IsFinite J.X.hom] [Etale J.X.hom]

def extendedGroupMap
    (α : (Over.pullback j).mapGrp.obj H ⟶ (Over.pullback j).mapGrp.obj J) : H.X ⟶ J.X :=
  ((baseChange j).preimage
    (ObjectProperty.homMk α.hom.hom :
      (baseChange j).obj (coefficientCover H) ⟶
        (baseChange j).obj (coefficientCover J))).hom

omit [(baseChange j).Full] [(baseChange j).Faithful] in
theorem extendedGroupMap_pullback [(baseChange j).Full] [(baseChange j).Faithful]
    (α : (Over.pullback j).mapGrp.obj H ⟶ (Over.pullback j).mapGrp.obj J) :
    (Over.pullback j).map (extendedGroupMap j H J α) = α.hom.hom :=
  congrArg (fun q => q.hom) ((baseChange j).map_preimage
    (ObjectProperty.homMk α.hom.hom :
      (baseChange j).obj (coefficientCover H) ⟶
        (baseChange j).obj (coefficientCover J)))

instance extendedGroupMap_isMonHom
    (α : (Over.pullback j).mapGrp.obj H ⟶ (Over.pullback j).mapGrp.obj J) :
    IsMonHom (extendedGroupMap j H J α) := by
  have h1 (T : Scheme.FiniteEtale X) : (1 : T.obj ⟶ H.X) ≫ extendedGroupMap j H J α = 1 := by
    apply finite_pullback_map_ext j T (coefficientCover J)
    rw [Functor.map_comp, extendedGroupMap_pullback, Functor.map_one, Functor.map_one,
      MonObj.one_comp]
  have hm (T : Scheme.FiniteEtale X) (a b : T.obj ⟶ H.X) :
      (a * b) ≫ extendedGroupMap j H J α =
        (a ≫ extendedGroupMap j H J α) * (b ≫ extendedGroupMap j H J α) := by
    apply finite_pullback_map_ext j T (coefficientCover J)
    rw [Functor.map_comp, extendedGroupMap_pullback, Functor.map_mul,
      Functor.map_mul, Functor.map_comp, Functor.map_comp,
      extendedGroupMap_pullback, MonObj.mul_comp]
  constructor
  · change η[H.X] ≫ extendedGroupMap j H J α = η[J.X]
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact h1 (𝟙_ (Scheme.FiniteEtale X))
  · rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]
    exact hm (coefficientCover H ⊗ coefficientCover H) _ _

def extendedGroupHom
    (α : (Over.pullback j).mapGrp.obj H ⟶ (Over.pullback j).mapGrp.obj J) : H ⟶ J :=
  Grp.homMk (extendedGroupMap j H J α)

theorem extendedGroupHom_pullback
    (α : (Over.pullback j).mapGrp.obj H ⟶ (Over.pullback j).mapGrp.obj J) :
    (Over.pullback j).mapGrp.map (extendedGroupHom j H J α) = α :=
  Grp.hom_ext _ _ (extendedGroupMap_pullback j H J α)

def extendedGroupIso
    (e : (Over.pullback j).mapGrp.obj H ≅ (Over.pullback j).mapGrp.obj J) : H ≅ J where
  hom := extendedGroupHom j H J e.hom
  inv := extendedGroupHom j J H e.inv
  hom_inv_id := by
    apply Grp.hom_ext
    apply finite_pullback_map_ext j (coefficientCover H)
      (coefficientCover H)
    change (Over.pullback j).map (extendedGroupMap j H J e.hom ≫
      extendedGroupMap j J H e.inv) = (Over.pullback j).map (𝟙 H.X)
    rw [Functor.map_comp, extendedGroupMap_pullback, extendedGroupMap_pullback,
      CategoryTheory.Functor.map_id]
    exact congrArg (fun q => q.hom.hom) e.hom_inv_id
  inv_hom_id := by
    apply Grp.hom_ext
    apply finite_pullback_map_ext j (coefficientCover J)
      (coefficientCover J)
    change (Over.pullback j).map (extendedGroupMap j J H e.inv ≫
      extendedGroupMap j H J e.hom) = (Over.pullback j).map (𝟙 J.X)
    rw [Functor.map_comp, extendedGroupMap_pullback, extendedGroupMap_pullback,
      CategoryTheory.Functor.map_id]
    exact congrArg (fun q => q.hom.hom) e.inv_hom_id

theorem extendedGroupIso_pullback
    (e : (Over.pullback j).mapGrp.obj H ≅ (Over.pullback j).mapGrp.obj J) :
    (Over.pullback j).mapGrp.mapIso (extendedGroupIso j H J e) = e := by
  apply Iso.ext
  exact extendedGroupHom_pullback j H J e.hom

end GroupExtension

end AlgebraicGeometry.Scheme.Group.BaseChange
