/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Algebra.DirectImage
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Original direct-image structure-algebra maps

Scheme maps over a fixed base induce contravariant maps of the actual direct-image
structure modules. The definition uses the original structure unit, direct-image
composition, and equality comparison. The resulting functor does not change any
underlying module; every original map is a native commutative-monoid map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.Scheme.Modules.Algebra

variable {X Y Z W : Scheme.{u}} {p : Y ⟶ X} {q : Z ⟶ X} {r : W ⟶ X}

/-- The original contravariant structure-module map associated to a map over the base. -/
def structurePullbackMap (k : Z ⟶ Y) (w : k ≫ p = q) :
    Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf p)
      (pushforwardStructureSheaf q) :=
  (pushforward p).map (SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
    (pushforwardComp k p).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (pushforwardCongr w).hom.app (SheafOfModules.unit Z.ringCatSheaf)

/-- On a literal composite the map is the original scheme component on the inverse-image open. -/
@[simp] theorem structurePullbackMap_comp_app (k : Z ⟶ Y) (p : Y ⟶ X)
    (U : X.Opens) (m : Γ(Y, p ⁻¹ᵁ U)) :
    (structurePullbackMap k rfl).app U m = (k.app (p ⁻¹ᵁ U)) m := by
  simp only [structurePullbackMap, Hom.comp_app, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app,
    eqToHom_refl, op_id, AddCommGrpCat.comp_apply]
  change (Z.presheaf.map (𝟙 (op (k ⁻¹ᵁ (p ⁻¹ᵁ U)))))
    ((k.app (p ⁻¹ᵁ U)) m) = _
  rw [Z.presheaf.map_id]
  rfl

/-- The identity map of a scheme gives the identity of its original structure direct image. -/
@[simp] theorem structurePullbackMap_id (p : Y ⟶ X) :
    structurePullbackMap (𝟙 Y) (Category.id_comp p) = 𝟙 (pushforwardStructureSheaf p) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  simp only [structurePullbackMap, Hom.comp_app, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app]
  change (Y.presheaf.map (eqToHom _).op) ((Scheme.Hom.app (𝟙 Y) (p ⁻¹ᵁ U)) m) = m
  simp only [Scheme.Hom.id_app, eqToHom_refl, op_id]
  let m₀ : Γ(Y, p ⁻¹ᵁ U) := m
  exact congrArg (fun f : Γ(Y, p ⁻¹ᵁ U) ⟶ Γ(Y, p ⁻¹ᵁ U) => f m₀)
    (Y.presheaf.map_id (op (p ⁻¹ᵁ U)))

/-- Composition retains the original structure-module maps, in their contravariant order. -/
@[reassoc] theorem structurePullbackMap_comp (k : Z ⟶ Y) (w : k ≫ p = q)
    (l : W ⟶ Z) (v : l ≫ q = r) :
    CategoryStruct.comp (obj := X.Modules)
      (structurePullbackMap k w) (structurePullbackMap l v) =
      structurePullbackMap (p := p) (q := r) (l ≫ k)
        (by rw [Category.assoc, w, v]) := by
  subst q
  subst r
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  simp only [Hom.comp_app, AddCommGrpCat.comp_apply, structurePullbackMap_comp_app]
  simp only [structurePullbackMap, Hom.comp_app, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app]
  change (l.app ((k ≫ p) ⁻¹ᵁ U)) ((k.app (p ⁻¹ᵁ U)) m) =
    (W.presheaf.map (eqToHom _).op) (((l ≫ k).app (p ⁻¹ᵁ U)) m)
  simp only [eqToHom_refl, op_id, Scheme.Hom.comp_app, CommRingCat.comp_apply]
  let m₀ : Γ(W, l ⁻¹ᵁ (k ⁻¹ᵁ (p ⁻¹ᵁ U))) :=
    (l.app (k ⁻¹ᵁ (p ⁻¹ᵁ U))) ((k.app (p ⁻¹ᵁ U)) m)
  exact (congrArg (fun f : Γ(W, l ⁻¹ᵁ (k ⁻¹ᵁ (p ⁻¹ᵁ U))) ⟶
    Γ(W, l ⁻¹ᵁ (k ⁻¹ᵁ (p ⁻¹ᵁ U))) => f m₀)
      (W.presheaf.map_id (op (l ⁻¹ᵁ (k ⁻¹ᵁ (p ⁻¹ᵁ U)))))).symm

/-- An original map of schemes preserves the native unit and multiplication. -/
instance instIsMonHomStructurePullbackMap (k : Z ⟶ Y) (w : k ≫ p = q) :
    IsMonHom (C := X.Modules) (structurePullbackMap k w) where
  one_hom := by
    subst q
    apply Scheme.Modules.hom_ext
    intro U
    ext a
    change (structurePullbackMap k rfl).app U ((p.app U) a) = ((k ≫ p).app U) a
    rw [structurePullbackMap_comp_app, Scheme.Hom.comp_app]
    rfl
  mul_hom := by
    subst q
    apply moduleTensor_hom_ext
    intro U m n
    let m₀ : Γ(Y, p ⁻¹ᵁ U) := m
    let n₀ : Γ(Y, p ⁻¹ᵁ U) := n
    change (structurePullbackMap k rfl).app U
      ((pushforwardStructureMul p).app U (moduleTensorSection X _ _ U m₀ n₀)) =
        (pushforwardStructureMul (k ≫ p)).app U
          ((tensorSheafMap X (structurePullbackMap k rfl)
            (structurePullbackMap k rfl)).val.app (op U)
            (moduleTensorSection X _ _ U m₀ n₀))
    have ht := tensorSheafMap_tmul X (structurePullbackMap k rfl)
      (structurePullbackMap k rfl) (op U) m₀ n₀
    change (tensorSheafMap X (structurePullbackMap k rfl)
      (structurePullbackMap k rfl)).val.app (op U)
        (moduleTensorSection X _ _ U m₀ n₀) =
      moduleTensorSection X _ _ U ((structurePullbackMap k rfl).app U m₀)
        ((structurePullbackMap k rfl).app U n₀) at ht
    have hleft := (congrArg ((structurePullbackMap k rfl).app U)
      (pushforwardStructureMul_app p U m₀ n₀)).trans
        (structurePullbackMap_comp_app k p U ((m₀ : Γ(Y, p ⁻¹ᵁ U)) * n₀))
    have hright := (congrArg ((pushforwardStructureMul (k ≫ p)).app U) ht).trans
      (pushforwardStructureMul_app (k ≫ p) U
        ((structurePullbackMap k rfl).app U m₀) ((structurePullbackMap k rfl).app U n₀))
    have hc := congrArg₂ (fun a b : Γ(Z, (k ≫ p) ⁻¹ᵁ U) => a * b)
      (structurePullbackMap_comp_app k p U m₀).symm
      (structurePullbackMap_comp_app k p U n₀).symm
    exact hleft.trans ((map_mul (k.app (p ⁻¹ᵁ U)).hom m₀ n₀).trans (hc.trans hright.symm))

/-- The actual structure direct-image module functor on the opposite category over a scheme. -/
def structureSheafFunctor (X : Scheme.{u}) : (Over X)ᵒᵖ ⥤ X.Modules where
  obj P := pushforwardStructureSheaf P.unop.hom
  map f := structurePullbackMap f.unop.left f.unop.w
  map_id P := structurePullbackMap_id P.unop.hom
  map_comp f g := (structurePullbackMap_comp f.unop.left f.unop.w
    g.unop.left g.unop.w).symm

/-- Every original component of the structure direct-image functor is an algebra-object map. -/
instance instIsMonHomStructureSheafFunctorMap {P Q : (Over X)ᵒᵖ} (f : P ⟶ Q) :
    IsMonHom (C := X.Modules) (show pushforwardStructureSheaf P.unop.hom ⟶
      pushforwardStructureSheaf Q.unop.hom from (structureSheafFunctor X).map f) :=
  instIsMonHomStructurePullbackMap f.unop.left f.unop.w

/-- Isomorphisms over the base induce isomorphisms of the original structure modules. -/
instance instIsIsoStructurePullbackMap (k : Z ⟶ Y) (w : k ≫ p = q) [IsIso k] :
    IsIso (C := X.Modules) (structurePullbackMap k w) := by
  let a : Over.mk q ⟶ Over.mk p := Over.homMk k w
  let hUnderlying : IsIso ((Over.forget X).map a) := inferInstanceAs (IsIso k)
  let hIso : IsIso a := isIso_of_reflects_iso a (Over.forget X)
  change IsIso ((structureSheafFunctor X).map a.op)
  infer_instance

/-- The same contravariant functor valued in native commutative algebra objects. -/
def structureAlgebraFunctor (X : Scheme.{u}) : (Over X)ᵒᵖ ⥤ CommMon X.Modules where
  obj P := pushforwardStructureAlgebra P.unop.hom
  map f := CommMon.homMk
    { hom := (structureSheafFunctor X).map f
      isMonHom_hom := instIsMonHomStructurePullbackMap f.unop.left f.unop.w }
  map_id P := by
    apply CommMon.hom_ext
    exact (structureSheafFunctor X).map_id P
  map_comp f g := by
    apply CommMon.hom_ext
    exact (structureSheafFunctor X).map_comp f g

/-- Forgetting the algebra structure gives literally the original direct-image module functor. -/
theorem structureAlgebraFunctor_comp_forget (X : Scheme.{u}) :
    structureAlgebraFunctor X ⋙ CommMon.forget X.Modules = structureSheafFunctor X := rfl

end AlgebraicGeometry.Scheme.Modules.Algebra
