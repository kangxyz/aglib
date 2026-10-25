/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.Global.NormalModelChart
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.GenericExtension

/-! # Actual global normal models of original generic trivializations

An original generic trivialization on an actual normal integral chart passes
to the whole-base relative normalization. Its original open chart identifies
the actual function fields, preserving the supplied generic point, full
structural triangle and finite constant coefficient. Finiteness of this
normalization is not asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global

universe u

attribute [local instance] hasSheafifyLarge

section FieldTransport

variable {C N : Scheme.{u}} [IsIntegral C] [IsIntegral N]
  (c : C ⟶ N) [IsOpenImmersion c]

/-- The isomorphism induced by the original native function-field map. -/
def chartGenericPointIso : Spec C.functionField ≅ Spec N.functionField := by
  haveI : IsDominant c := Scheme.isDominant_of_isOpenImmersion c
  haveI : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap c)) :=
    Scheme.FunctionField.fieldMap_isIso c
  exact Scheme.Spec.mapIso (asIso (CommRingCat.ofHom (Scheme.functionFieldMap c))).op

/-- The original generic inclusion square, with its supplied original chart. -/
@[reassoc]
theorem chartGenericPointIso_hom_over :
    (chartGenericPointIso c).hom ≫ N.fromSpecStalk (genericPoint N) =
      C.fromSpecStalk (genericPoint C) ≫ c := by
  have : IsDominant c := Scheme.isDominant_of_isOpenImmersion c
  exact (Scheme.fromSpecStalk_genericPoint_naturality c).symm

/-- The inverse generic-field isomorphism retains the whole original square. -/
@[reassoc]
theorem chartGenericPointIso_inv_over :
    (chartGenericPointIso c).inv ≫ C.fromSpecStalk (genericPoint C) ≫ c =
      N.fromSpecStalk (genericPoint N) := by
  let e := chartGenericPointIso c
  exact (congrArg (fun k => e.inv ≫ k) (chartGenericPointIso_hom_over c).symm).trans
    ((Category.assoc e.inv e.hom (N.fromSpecStalk (genericPoint N))).symm.trans
      ((congrArg (fun k => k ≫ N.fromSpecStalk (genericPoint N)) e.inv_hom_id).trans
        (Category.id_comp _)))

end FieldTransport

/-- A genuinely global normal integral model, with its original generic
point of the original stratum and literal finite constant trivialization.
Its original map is integral and can be infinite. -/
structure GlobalNormalGenericModel {X S : Scheme.{u}} (s : S ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) where
  source : Scheme.{u}
  [source_integral : IsIntegral source]
  normal_stalk : ∀ x : source, IsIntegrallyClosed (source.presheaf.stalk x)
  morphism : source ⟶ X
  [morphism_integral : IsIntegralHom morphism]
  value : AddCommGrpCat.{u}
  [value_finite : Finite value]
  point : Spec source.functionField ⟶ S
  [point_dominant : IsDominant point]
  over : point ≫ s = source.fromSpecStalk (genericPoint source) ≫ morphism
  trivialization :
    (inverseImage (source.fromSpecStalk (genericPoint source) ≫ morphism)).obj F ≅
      ConstantFinite.coefficient value (Spec source.functionField)

attribute [instance] GlobalNormalGenericModel.source_integral
  GlobalNormalGenericModel.normal_stalk GlobalNormalGenericModel.morphism_integral
  GlobalNormalGenericModel.value_finite GlobalNormalGenericModel.point_dominant

/-- A supplied original generic trivialization on an actual integral normal
chart globalizes via its actual relative normalization over the entire base.
No global model, finite normalization, or identification of an arbitrary
field with the normalization function field is assumed. -/
def globalNormalGenericModelOfIntegralChart
    {C U X S : Scheme.{u}} [IsIntegral C]
    [∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)]
    (g : C ⟶ U) [IsIntegralHom g] (j : U ⟶ X) [IsOpenImmersion j]
    (s : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (B : AddCommGrpCat.{u}) [Finite B]
    (ζ : Spec C.functionField ⟶ S) [IsDominant ζ]
    (hζ : ζ ≫ s = (C.fromSpecStalk (genericPoint C) ≫ g) ≫ j)
    (eB : (inverseImage ((C.fromSpecStalk (genericPoint C) ≫ g) ≫ j)).obj F ≅
      ConstantFinite.coefficient B (Spec C.functionField)) : GlobalNormalGenericModel s F := by
  let f := (C.fromSpecStalk (genericPoint C) ≫ g) ≫ j
  let N := f.normalization
  let c : C ⟶ N := normalGenericOpenChart g j
  let e := chartGenericPointIso c
  have hc : C.fromSpecStalk (genericPoint C) ≫ c = f.toNormalization :=
    normalGenericOpenChart_generic g j
  have he : e.inv ≫ f.toNormalization = N.fromSpecStalk (genericPoint N) :=
    (congrArg (fun k => e.inv ≫ k) hc.symm).trans (chartGenericPointIso_inv_over c)
  have hfx : e.inv ≫ f = N.fromSpecStalk (genericPoint N) ≫ f.fromNormalization :=
    (congrArg (fun k => e.inv ≫ k) f.toNormalization_fromNormalization.symm).trans
      ((Category.assoc e.inv f.toNormalization f.fromNormalization).symm.trans
        (congrArg (fun k => k ≫ f.fromNormalization) he))
  refine {
    source := N
    normal_stalk := fun x => (fieldNormalization_stalk_normal_domain C.functionField f x).1
    morphism := f.fromNormalization
    value := B
    point := e.inv ≫ ζ
    over := (Category.assoc e.inv ζ s).trans
      ((congrArg (fun k => e.inv ≫ k) hζ).trans hfx)
    trivialization := ?_ }
  exact eqToIso (congrArg (fun k => (inverseImage k).obj F) hfx.symm) ≪≫
    (inverseImageComp f e.inv).app F ≪≫ (inverseImage e.inv).mapIso eB ≪≫
      (inverseImageConstantIso e.inv).app (ConstantFinite.value B)

namespace GlobalNormalGenericModel

variable {X S : Scheme.{u}} {s : S ⟶ X} {F : AbelianSheaf.{u, u + 1} X}

/-- The original generic adjoint extended over the actual global normal model. -/
def extensionMap (m : GlobalNormalGenericModel s F) :
    F ⟶ (directImage m.morphism).obj (ConstantFinite.coefficient m.value m.source) :=
  extendGenericMap m.morphism F (ConstantFinite.value m.value) m.trivialization.hom

@[reassoc]
theorem extensionMap_comp (m : GlobalNormalGenericModel s F) :
    m.extensionMap ≫
      (directImage m.morphism).map
        (NormalConstants.constantGenericIso m.source (ConstantFinite.value m.value)).hom ≫
      (directImageCompIso m.morphism (m.source.fromSpecStalk (genericPoint m.source))).hom.app _ =
    (inverseImageAdjunction (m.source.fromSpecStalk (genericPoint m.source) ≫ m.morphism)).homEquiv
      F _ m.trivialization.hom :=
  extendGenericMap_comp m.morphism F (ConstantFinite.value m.value) m.trivialization.hom

end GlobalNormalGenericModel
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteCogenerators.Global
