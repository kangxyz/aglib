/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FunctionField.Normalization
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-!
# Generic restriction of finite etale schemes

Over an integral scheme with integrally closed stalks, actual generic base change is full
and faithful on the native category of finite etale schemes. The extension and Hom-set
equivalence use literal pullback maps. Existence of new covers is not asserted.

## Extraction basis

Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/GenericFullFaithfulness.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`56316f6517043fcd7e709e55d04765986ce74140b7d0d4e98e59a4648ec25c47`.
The source statements, binder universes, hypotheses and chosen maps are retained.
Direct Mathlib carriers/maps replace the recorded source wrappers; source-token correspondence
and those definitional substitutions are separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange baseChange_obj_hom)

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  (Y Z : Scheme.FiniteEtale X)

/-- The underlying generic-fibre map is composed with the actual pullback projections. -/
def genericFiberMapToScheme
    (h : (baseChange (X.fromSpecStalk (genericPoint X))).obj Y ⟶
      (baseChange (X.fromSpecStalk (genericPoint X))).obj Z) :
    pullback (X.fromSpecStalk (genericPoint X)) Y.obj.hom ⟶ Z.obj.left :=
  (pullbackSymmetry (X.fromSpecStalk (genericPoint X)) Y.obj.hom).hom ≫
    h.hom.left ≫ pullback.fst Z.obj.hom (X.fromSpecStalk (genericPoint X))

omit [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] in
/-- The underlying generic-fibre map respects the structural morphisms to the base. -/
theorem genericFiberMapToScheme_over
    (h : (baseChange (X.fromSpecStalk (genericPoint X))).obj Y ⟶
      (baseChange (X.fromSpecStalk (genericPoint X))).obj Z) :
    genericFiberMapToScheme X Y Z h ≫ Z.obj.hom =
      pullback.snd (X.fromSpecStalk (genericPoint X)) Y.obj.hom ≫ Y.obj.hom := by
  have hw : h.hom.left ≫ pullback.snd Z.obj.hom (X.fromSpecStalk (genericPoint X)) =
      pullback.snd Y.obj.hom (X.fromSpecStalk (genericPoint X)) := by
    simpa only [baseChange_obj_hom] using Over.w h.hom
  simp only [genericFiberMapToScheme, Category.assoc, pullback.condition]
  rw [← Category.assoc h.hom.left, hw]
  simp only [pullbackSymmetry_hom_comp_snd_assoc]
  exact pullback.condition

/-- Extend an actual morphism of the literal generic finite-etale covers. -/
def extendGenericFiberMap
    (h : (baseChange (X.fromSpecStalk (genericPoint X))).obj Y ⟶
      (baseChange (X.fromSpecStalk (genericPoint X))).obj Z) : Y ⟶ Z :=
  ObjectProperty.homMk (Over.homMk
    (_root_.AlgebraicGeometry.Scheme.extendFromGenericFiber X Y.obj.hom Z.obj.hom
      (genericFiberMapToScheme X Y Z h) (genericFiberMapToScheme_over X Y Z h))
    (_root_.AlgebraicGeometry.Scheme.extendFromGenericFiber_over X Y.obj.hom Z.obj.hom
      (genericFiberMapToScheme X Y Z h) (genericFiberMapToScheme_over X Y Z h)))

/-- The extended map has precisely the given literal generic base change. -/
theorem baseChange_extendGenericFiberMap
    (h : (baseChange (X.fromSpecStalk (genericPoint X))).obj Y ⟶
      (baseChange (X.fromSpecStalk (genericPoint X))).obj Z) :
    (baseChange (X.fromSpecStalk (genericPoint X))).map (extendGenericFiberMap X Y Z h) = h := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  dsimp [baseChange, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget, Over.pullback]
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
    apply (cancel_epi (pullbackSymmetry (X.fromSpecStalk (genericPoint X)) Y.obj.hom).hom).mp
    dsimp only [extendGenericFiberMap, ObjectProperty.homMk, Over.homMk,
      CostructuredArrow.homMk, Over.Hom.left]
    simpa only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
      genericFiberMapToScheme] using
      _root_.AlgebraicGeometry.Scheme.extendFromGenericFiber_comp X Y.obj.hom Z.obj.hom
        (genericFiberMapToScheme X Y Z h) (genericFiberMapToScheme_over X Y Z h)
  · simp only [pullback.lift_snd]
    exact (Over.w h.hom).symm

/-- Generic restriction is faithful on actual finite-etale scheme maps. -/
theorem genericFiber_hom_ext {f g : Y ⟶ Z}
    (h : (baseChange (X.fromSpecStalk (genericPoint X))).map f =
      (baseChange (X.fromSpecStalk (genericPoint X))).map g) : f = g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply _root_.AlgebraicGeometry.Scheme.genericFiber_hom_ext X Y.obj.hom Z.obj.hom (Over.w f.hom)
      (Over.w g.hom)
  have hs := congrArg (fun t => (pullbackSymmetry (X.fromSpecStalk (genericPoint X)) Y.obj.hom).hom
      ≫
    t.hom.left ≫ pullback.fst Z.obj.hom (X.fromSpecStalk (genericPoint X))) h
  simpa [baseChange, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget, Over.pullback,
    Category.assoc] using hs

/-- Generic base change is full on the supplied finite etale schemes. -/
instance instFullBaseChangeGenericPoint : (baseChange (X.fromSpecStalk (genericPoint X))).Full where
  map_surjective h := ⟨extendGenericFiberMap X _ _ h, baseChange_extendGenericFiberMap X _ _ h⟩

/-- Actual generic restriction is faithful under the same normality conditions. -/
instance instFaithfulBaseChangeGenericPoint : (baseChange (X.fromSpecStalk (genericPoint
    X))).Faithful where
  map_injective := genericFiber_hom_ext X _ _

/-- The concrete Hom-set equivalence uses literal scheme base change. -/
def genericFiberHomEquiv : (Y ⟶ Z) ≃
    ((baseChange (X.fromSpecStalk (genericPoint X))).obj Y ⟶ (baseChange (X.fromSpecStalk
        (genericPoint X))).obj Z) where
  toFun := (baseChange (X.fromSpecStalk (genericPoint X))).map
  invFun := extendGenericFiberMap X Y Z
  left_inv _f := genericFiber_hom_ext X Y Z (baseChange_extendGenericFiberMap X Y Z _)
  right_inv := baseChange_extendGenericFiberMap X Y Z

end AlgebraicGeometry.Scheme.FiniteEtale
