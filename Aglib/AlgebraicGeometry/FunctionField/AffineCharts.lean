/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.StalkMap
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Actual function fields of affine and common open charts

Source: packet R5Lab.Aglib.AlgebraicGeometry.FunctionField.AffineCharts.
Native functionFieldMap and functionFieldConstants are reused. The original
generic-arrow definition of constants is proved equal to that native map.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme

/-- Structural constants recover the original generic-point structural arrow. -/
theorem functionFieldConstants_specMap {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) :
    Spec.map (CommRingCat.ofHom (functionFieldConstants X p)) =
      X.fromSpecStalk (genericPoint X) ≫ p := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have hg : (X.fromSpecStalk (genericPoint X)).appTop ≫
      (Scheme.ΓSpecIso X.functionField).hom = X.germToFunctionField ⊤ := by
    simpa [functionFieldSectionsIso] using
      fromSpecStalk_genericPoint_app_functionFieldSectionsIso X ⊤
  apply ext_to_Spec
  change (Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom (functionFieldConstants X p))).appTop =
    (Scheme.ΓSpecIso (.of k)).inv ≫ (X.fromSpecStalk (genericPoint X) ≫ p).appTop
  rw [← Scheme.ΓSpecIso_inv_naturality, Scheme.Hom.comp_appTop]
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫ X.germToFunctionField ⊤) ≫ _ = _
  rw [← hg]
  simp only [Category.assoc]
  change (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
      (X.fromSpecStalk (genericPoint X)).appTop ≫
      ((Scheme.ΓSpecIso X.functionField).hom ≫ (Scheme.ΓSpecIso X.functionField).inv) = _
  rw [Iso.hom_inv_id, Category.comp_id]

/-- The packet's generic-arrow constants are the existing native germ constants. -/
theorem functionFieldConstants_eq_specPreimage {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) :
    functionFieldConstants X p =
      (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom (functionFieldConstants X p)) =
    Spec.map (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p))
  rw [functionFieldConstants_specMap, Spec.map_preimage]

/-- Functoriality on the actual generic stalk maps. -/
theorem functionFieldMap_comp {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    functionFieldMap (f ≫ g) = (functionFieldMap f).comp (functionFieldMap g) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  apply (cancel_mono (Z.fromSpecStalk (genericPoint Z))).mp
  change Spec.map (CommRingCat.ofHom (functionFieldMap (f ≫ g))) ≫ _ =
    Spec.map (CommRingCat.ofHom (functionFieldMap g) ≫
      CommRingCat.ofHom (functionFieldMap f)) ≫ _
  rw [Spec.map_comp, Category.assoc,
    ← fromSpecStalk_genericPoint_naturality g, ← Category.assoc,
    ← fromSpecStalk_genericPoint_naturality f,
    ← fromSpecStalk_genericPoint_naturality (f ≫ g), Category.assoc]

/-- An open immersion between the actual integral schemes is dominant. -/
theorem isDominant_of_isOpenImmersion {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsOpenImmersion f] :
    IsDominant f := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure Y, ← AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion f]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint X, rfl⟩)

namespace FunctionField
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsOpenImmersion f]
local instance : IsDominant f := Scheme.isDominant_of_isOpenImmersion f
theorem fieldMap_isIso :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) := by
  change IsIso (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap (genericPoint X))
  have he : Y.presheaf.stalkSpecializes
      (specializes_of_eq (Scheme.map_genericPoint_of_isDominant X f)) =
      (Y.presheaf.stalkCongr (.of_eq
        (Scheme.map_genericPoint_of_isDominant X f).symm)).hom := rfl
  rw [he]
  infer_instance
def fieldEquiv : Y.functionField ≃+* X.functionField := by
  let := fieldMap_isIso f
  exact (asIso (CommRingCat.ofHom
    (Scheme.functionFieldMap f))).commRingCatIsoToRingEquiv
@[simp] theorem fieldEquiv_apply (a : Y.functionField) :
    fieldEquiv f a = Scheme.functionFieldMap f a := rfl
def affineFieldEquiv (A : CommRingCat.{u}) [IsDomain A]
    (j : Spec A ⟶ Y) [IsOpenImmersion j] :
    Y.functionField ≃+* FractionRing A :=
  (fieldEquiv j).trans
    (FractionRing.algEquiv A (Spec A).functionField).symm.toRingEquiv

theorem fieldEquiv_generic_triangle :
    X.fromSpecStalk (genericPoint X) ≫ f =
      Spec.map (CommRingCat.ofHom (fieldEquiv f).toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y) := by
  change X.fromSpecStalk _ ≫ f =
    Spec.map (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _) ≫
      Y.fromSpecStalk _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm

theorem fieldEquiv_constants (k : Type u) [Field k] (p : Y ⟶ Spec (.of k)) :
    (fieldEquiv f).toRingHom.comp (functionFieldConstants _ p) =
      functionFieldConstants _ (f ≫ p) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom (functionFieldConstants _ p) ≫
      CommRingCat.ofHom (fieldEquiv f).toRingHom) =
    Spec.map (CommRingCat.ofHom (functionFieldConstants X (f ≫ p)))
  rw [Spec.map_comp, functionFieldConstants_specMap, functionFieldConstants_specMap,
    ← Category.assoc, ← fieldEquiv_generic_triangle]
  simp only [Category.assoc]

theorem affine_constants (A : CommRingCat.{u}) [IsDomain A]
    (k : Type u) [Field k] [Algebra k A] :
    functionFieldConstants (Spec A) (Spec.map (CommRingCat.ofHom (algebraMap k A))) =
      (algebraMap A (Spec A).functionField).comp (algebraMap k A) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom (functionFieldConstants (Spec A)
      (Spec.map (CommRingCat.ofHom (algebraMap k A))))) =
    Spec.map (CommRingCat.ofHom (algebraMap k A) ≫
      CommRingCat.ofHom (algebraMap A (Spec A).functionField))
  rw [functionFieldConstants_specMap, Spec.map_comp, Spec.fromSpecStalk_eq']
  rfl

theorem affineFieldEquiv_constants (A : CommRingCat.{u}) [IsDomain A]
    (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (k : Type u) [Field k] [Algebra k A]
    (p : Y ⟶ Spec (.of k))
    (h : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k A))) (a : k) :
    affineFieldEquiv A j (functionFieldConstants _ p a) = algebraMap k (FractionRing A) a := by
  change (FractionRing.algEquiv A (Spec A).functionField).symm
    (fieldEquiv j (functionFieldConstants _ p a)) = _
  have hc := DFunLike.congr_fun (fieldEquiv_constants j k p) a
  change fieldEquiv j (functionFieldConstants _ p a) = functionFieldConstants _ (j ≫ p) a at hc
  rw [hc, h, affine_constants A k]
  simp only [RingHom.comp_apply, AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_eq k A (FractionRing A)]
  rfl

end FunctionField
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FunctionField
variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (sx : X ⟶ Spec (.of k)) (sy : Y ⟶ Spec (.of k))
  (φ : Y.functionField →+* X.functionField)

def genericMap : Spec X.functionField ⟶ Y :=
  Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk (genericPoint Y)

theorem genericMap_over
    (hφ : φ.comp (functionFieldConstants _ sy) = functionFieldConstants _ sx) :
    genericMap φ ≫ sy = X.fromSpecStalk (genericPoint X) ≫ sx := by
  unfold genericMap
  rw [Category.assoc, ← functionFieldConstants_specMap sy, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (φ.comp (functionFieldConstants _ sy))) = _
  rw [hφ, functionFieldConstants_specMap]

end AlgebraicGeometry.Scheme.FunctionField.GenericExtension
namespace AlgebraicGeometry.Scheme.FunctionField.CommonChart
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.FunctionField
variable {k : Type u} [Field k] {A X Y : Scheme.{u}}
  [IsIntegral A] [IsIntegral X] [IsIntegral Y]
  (sx : X ⟶ Spec (.of k)) (sy : Y ⟶ Spec (.of k))
  (jX : A ⟶ X) (jY : A ⟶ Y) [IsOpenImmersion jX] [IsOpenImmersion jY]

def chartFieldEquiv : Y.functionField ≃+* X.functionField :=
  (fieldEquiv jY).trans (fieldEquiv jX).symm

theorem chartFieldEquiv_constants (hc : jX ≫ sx = jY ≫ sy) :
    (chartFieldEquiv jX jY).toRingHom.comp (functionFieldConstants _ sy) =
      functionFieldConstants _ sx := by
  ext a
  apply (fieldEquiv jX).injective
  change fieldEquiv jX ((fieldEquiv jX).symm (fieldEquiv jY (functionFieldConstants _ sy a))) = _
  rw [RingEquiv.apply_symm_apply]
  have hx := DFunLike.congr_fun (fieldEquiv_constants jX k sx) a
  have hy := DFunLike.congr_fun (fieldEquiv_constants jY k sy) a
  change fieldEquiv jX (functionFieldConstants _ sx a) = functionFieldConstants _ (jX ≫ sx) a at hx
  change fieldEquiv jY (functionFieldConstants _ sy a) = functionFieldConstants _ (jY ≫ sy) a at hy
  rw [hx, hy, hc]

end AlgebraicGeometry.Scheme.FunctionField.CommonChart
