/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.HomLifts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleFixedSource
public import Mathlib.CategoryTheory.Filtered.Connected

/-! # Actual maps between fixed native module models

The actual fixed-coefficient colimit comparison turns a representative in the
native right-tail Hom cocone into a later map between the two original model
pullbacks. Its conclusion retains the original inverse-image triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
namespace FixedModelData

universe u

theorem cone_identity_leg {I C : Type*} [Category* I] [Category* C]
    (X : I ⥤ C) (i : I) (r : (Functor.const I).obj (X.obj i) ⟶ X)
    (hr : r.app i = 𝟙 (X.obj i)) {j : I} (a : i ⟶ j) : r.app j = X.map a := by
  have h : 𝟙 (X.obj i) ≫ r.app j = r.app i ≫ X.map a := r.naturality a
  exact ((Category.id_comp _).symm.trans h).trans
    ((congrArg (fun k : X.obj i ⟶ X.obj i => k ≫ X.map a) hr).trans (Category.id_comp _))

theorem triangle_target_transport
    {J : Type*} [Category* J] {A : J → Type*} [∀ j, Category* (A j)]
    (D : InjectiveSystem.AdjunctionData A) {x y t : J}
    (p : x ⟶ t) (q r : x ⟶ y) (a : y ⟶ t)
    (hq : q ≫ a = p) (hr : r ≫ a = p) (h : q = r) (B : A x) :
    (D.left a).map (eqToHom (congrArg (fun f => (D.left f).obj B) h)) ≫
      (D.triangleIso p r a hr).inv.app B = (D.triangleIso p q a hq).inv.app B := by
  cases h
  change (D.left a).map (𝟙 ((D.left q).obj B)) ≫
    (D.triangleIso p q a hr).inv.app B = (D.triangleIso p q a hq).inv.app B
  exact (congrArg (fun z => z ≫ (D.triangleIso p q a hr).inv.app B)
    ((D.left a).map_id ((D.left q).obj B))).trans (Category.id_comp _)

variable (R : Type (u + 1)) [Ring R]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (i : I)
    (r : (Functor.const I).obj (X.obj i) ⟶ X) (hr : r.app i = 𝟙 (X.obj i))
    (c : Cocone X) (hc : IsColimit c)

local instance : IsConnected I := IsFiltered.isConnected I

include hr in
theorem baseCone_fac (j : I) : r.app j ≫ c.ι.app j = c.ι.app i := by
  have h := nat_trans_from_is_connected (r ≫ c.ι) j i
  change r.app j ≫ c.ι.app j = r.app i ≫ c.ι.app i at h
  exact h.trans ((congrArg (fun k : X.obj i ⟶ X.obj i => k ≫ c.ι.app i) hr).trans
    (Category.id_comp (c.ι.app i)))


/-- The original fixed coefficient system's canonical limit comparison. -/
def limitIso (B : Coefficient R (X.obj i).unop)
    [HasColimit (coneCoefficientFunctor R X c
      (pullbackCoefficientSystem R X (Cone.mk (X.obj i) r) B))] :
    colimit (coneCoefficientFunctor R X c
      (pullbackCoefficientSystem R X (Cone.mk (X.obj i) r) B)) ≅
      (inverseImage R (c.ι.app i).unop).obj B :=
  pullbackLimitCoefficientIso R X (Cone.mk (X.obj i) r) B c (c.ι.app i)
    (baseCone_fac X i r hr c)

/-- Exact insertion into the original fixed coefficient colimit. -/
theorem limitIso_ι (B : Coefficient R (X.obj i).unop)
    [HasColimit (coneCoefficientFunctor R X c
      (pullbackCoefficientSystem R X (Cone.mk (X.obj i) r) B))] (j : I) :
    colimit.ι (coneCoefficientFunctor R X c
      (pullbackCoefficientSystem R X (Cone.mk (X.obj i) r) B)) j ≫
      (limitIso R X i r hr c B).hom =
      ((schemeAdjunctionData R).triangleIso (c.ι.app i) (r.app j)
        (c.ι.app j) (baseCone_fac X i r hr c j)).inv.app B := by
  have h := pullbackLimitCoefficientIso_ι R X (Cone.mk (X.obj i) r) B c (c.ι.app i)
    (baseCone_fac X i r hr c) j
  change colimit.ι (coneCoefficientFunctor R X c
      (pullbackCoefficientSystem R X (Cone.mk (X.obj i) r) B)) j ≫
      (limitIso R X i r hr c B).hom = (𝟙 _) ≫
      ((schemeAdjunctionData R).triangleIso (c.ι.app i) (r.app j)
        (c.ι.app j) (baseCone_fac X i r hr c j)).inv.app B at h
  exact h.trans (Category.id_comp _)

end FixedModelData
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
