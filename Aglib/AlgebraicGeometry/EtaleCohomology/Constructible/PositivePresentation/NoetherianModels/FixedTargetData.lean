/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.FixedTargetTriangle
public import Mathlib.CategoryTheory.IsConnected

/-! # Original bounded targets pulled from a fixed model

A specified structural cone is the actual fixed-base datum. Native
coefficient-limit comparisons and adjunction units normalize the original
right-image-tail maps, both at stages and at the scheme limit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

open Continuity FixedTargetTriangle

private theorem rightTail_transition_unit
    {J : Type*} [Category* J] {A : J → Type*} [∀ j, Category* (A j)]
    (D : InjectiveSystem.AdjunctionData A) (F : InjectiveSystem.System D)
    {i j k : J} (a : i ⟶ j) (b : j ⟶ k) (t : i ⟶ k) (h : a ≫ b = t)
    {P : A i} (s : P ⟶ F.obj i) :
    (s ≫ F.map a) ≫ InjectiveSystem.System.rightTailTransition D F a b t h =
      s ≫ F.map t := by
  subst t
  simpa only [InjectiveSystem.System.rightTailTransition,
    InjectiveSystem.System.rightStep, eqToHom_refl, Category.comp_id, Category.assoc] using
    congrArg (fun k => s ≫ k) (InjectiveSystem.System.map_comp_inv D F a b)

variable {I : Type u} [SmallCategory I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (i : I) (r : (Functor.const I).obj (X.obj i) ⟶ X)
  (hr : r.app i = 𝟙 (X.obj i))

include hr in
/-- A structural cone with identity component retains every actual tail map. -/
theorem baseCone_leg (a : Under i) : r.app a.right = X.map a.hom := by
  exact cone_identity_leg X i r hr a.hom

/-- The original fixed bounded coefficient gives the native compatible system. -/
def baseCoefficientSystem (n : ℕ)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n) : DiagramCoefficientSystem X :=
  Stalk.pullbackCoefficientSystem X (Cone.mk (X.obj i) r) B.obj

theorem baseCoefficientSystem_killed (n : ℕ)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n) (j : I) :
    n • 𝟙 ((baseCoefficientSystem X i r n B).obj j) = 0 := by
  change n • 𝟙 ((inverseImage (r.app j).unop).obj B.obj) = 0
  simpa using congrArg (fun f => (inverseImage (r.app j).unop).map f) B.property

/-- Original identity comparison at the model base. -/
def baseIdentityIso :
    inverseImage (r.app i).unop ≅ 𝟭 (AbelianSheaf.{u, u + 1} (X.obj i).unop) :=
  eqToIso (congrArg inverseImage (congrArg Quiver.Hom.unop hr)) ≪≫
    inverseImageId (X.obj i).unop

/-- The actual later coefficient has its original structural-map comparison. -/
def baseStageIso (n : ℕ) (B : BoundedPresentation.Coefficient (X.obj i).unop n)
    (a : Under i) :
    (baseCoefficientSystem X i r n B).obj a.right ≅
      (inverseImage (X.map a.hom).unop).obj B.obj :=
  coefficientStageIso X (Cone.mk (X.obj i) r) B.obj a.right (X.map a.hom)
    (baseCone_leg X i r hr a)

/-- The actual original fixed coefficient unit into a later right image. -/
def baseRightTailUnit (n : ℕ)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n) (a : Under i) :
    B.obj ⟶ (diagramRightTail X (baseCoefficientSystem X i r n B) i).obj a :=
  (baseIdentityIso X i r hr).inv.app B.obj ≫ (baseCoefficientSystem X i r n B).map a.hom

/-- Original fixed-target units are natural for the actual right-tail transitions. -/
theorem baseRightTailUnit_naturality (n : ℕ)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n)
    {a b : Under i} (q : a ⟶ b) :
    baseRightTailUnit X i r hr n B a ≫
        (diagramRightTail X (baseCoefficientSystem X i r n B) i).map q =
      baseRightTailUnit X i r hr n B b := by
  let F := baseCoefficientSystem X i r n B
  let e : B.obj ⟶ F.obj i := (baseIdentityIso X i r hr).inv.app B.obj
  exact rightTail_transition_unit (diagramAdjunctionData X) F
    a.hom q.right b.hom (Under.w q) e

/-- After the original stage coefficient comparison, the displayed unit
is precisely the original inverse/direct-image adjunction unit. -/
theorem baseRightTailUnit_value (n : ℕ)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n) (a : Under i) :
    baseRightTailUnit X i r hr n B a ≫
      (directImage (X.map a.hom).unop).map (baseStageIso X i r hr n B a).hom =
        (inverseImageAdjunction (X.map a.hom).unop).unit.app B.obj := by
  let b : Cone X := Cone.mk (X.obj i) r
  let F := baseCoefficientSystem X i r n B
  let e : B.obj ⟶ F.obj i := (baseIdentityIso X i r hr).inv.app B.obj
  have hmap : F.map a.hom =
      (inverseImageAdjunction (X.map a.hom).unop).homEquiv _ _
        ((pullbackTriangleIso (r.app a.right).unop (r.app i).unop (X.map a.hom).unop
          (congrArg Quiver.Hom.unop (b.w a.hom))).inv.app B.obj) := rfl
  have hvalue :=
    adjoint_triangle_identity (r.app i).unop (congrArg Quiver.Hom.unop hr)
      (X.map a.hom).unop (r.app a.right).unop
      (congrArg Quiver.Hom.unop (b.w a.hom))
      (congrArg Quiver.Hom.unop (baseCone_leg X i r hr a)) B.obj
  have hfinal := (Category.assoc e (F.map a.hom)
    ((directImage (X.map a.hom).unop).map (baseStageIso X i r hr n B a).hom)).trans
      ((congrArg (fun k => e ≫ k ≫
        (directImage (X.map a.hom).unop).map (baseStageIso X i r hr n B a).hom) hmap).trans
          hvalue)
  exact hfinal

variable [IsFiltered I] (c : Cocone X)

include hr in
/-- The fixed-base cone and original limit cocone have their actual common composite. -/
theorem baseCone_fac (j : I) : r.app j ≫ c.ι.app j = c.ι.app i := by
  let : IsConnected I := IsFiltered.isConnected I
  have h := nat_trans_from_is_connected (r ≫ c.ι) j i
  change r.app j ≫ c.ι.app j = r.app i ≫ c.ι.app i at h
  exact h.trans ((congrArg (fun k : X.obj i ⟶ X.obj i => k ≫ c.ι.app i) hr).trans
    (Category.id_comp (c.ι.app i)))

local instance : IsConnected I := IsFiltered.isConnected I

include hr in
/-- Native original fixed-coefficient limit iso; no new limit comparison is chosen. -/
def baseLimitCoefficientIso (n : ℕ)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n) :
    colimit (coneCoefficientFunctor X c (baseCoefficientSystem X i r n B)) ≅
      (inverseImage (c.ι.app i).unop).obj B.obj :=
  Stalk.pullbackLimitCoefficientIso X (Cone.mk (X.obj i) r) c (c.ι.app i)
    (baseCone_fac X i r hr c) B.obj

/-- Every displayed fixed-target unit followed by the original limit leg
is the original unit at the structural limit projection. -/
theorem baseRightTailUnit_point (n : ℕ)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n) (a : Under i) :
    baseRightTailUnit X i r hr n B a ≫
        (diagramRightTailCocone X (baseCoefficientSystem X i r n B) c i).ι.app a ≫
        (directImage (c.ι.app i).unop).map (baseLimitCoefficientIso X i r hr c n B).hom =
      (inverseImageAdjunction (c.ι.app i).unop).unit.app B.obj := by
  let F := baseCoefficientSystem X i r n B
  let E := baseLimitCoefficientIso X i r hr c n B
  let e : B.obj ⟶ F.obj i := (baseIdentityIso X i r hr).inv.app B.obj
  let l := diagramRightTailLeg X F c a.hom
  have hleg : F.map a.hom ≫ l = diagramAdjointLeg X c F i :=
    (diagramAdjointLeg_naturality X c F a.hom).symm
  have hins :=
    Stalk.ι_pullbackLimitCoefficientIso_hom X (Cone.mk (X.obj i) r) c (c.ι.app i)
      (baseCone_fac X i r hr c) B.obj i
  have hunit :=
    adjoint_triangle_identity_same (r.app i).unop (congrArg Quiver.Hom.unop hr)
      (c.ι.app i).unop (congrArg Quiver.Hom.unop (baseCone_fac X i r hr c i)) B.obj
  have htrans0 :=
    ((inverseImageAdjunction (c.ι.app i).unop).homEquiv_naturality_right
      (colimit.ι (coneCoefficientFunctor X c F) i) E.hom).symm
  have htrans := htrans0.trans
    (congrArg ((inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _) hins)
  exact point_composition e (F.map a.hom) l ((directImage (c.ι.app i).unop).map E.hom)
    (diagramAdjointLeg X c F i) _ _ hleg htrans hunit

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
