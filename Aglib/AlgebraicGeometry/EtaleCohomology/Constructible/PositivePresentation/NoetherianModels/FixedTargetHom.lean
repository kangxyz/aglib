/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Filtered.AdjointStageHom
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.FixedTargetData

/-! # Original Hom descent for a fixed bounded model target

The native fixed-coefficient limit iso turns the actual bounded right-image
Hom cocone into actual later-stage maps between the original inverse images.
Its same original transitions detect eventual equality. No constructible
category equivalence or unbounded module descent theory is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

open Continuity FixedTargetTriangle

private theorem map_transport_comp {C D A : Type*} [Category* C] [Category* D]
    (L : C ⥤ D) (P : A → C) (Q : A → Prop) (Y : D)
    (m : ∀ a, Q a → (L.obj (P a) ⟶ Y))
    (q r : A) (hq : Q q) (hr : Q r) (h : q = r) :
    L.map (eqToHom (congrArg P h)) ≫ m r hr = m q hq := by
  cases h
  simp only [eqToHom_refl, L.map_id, Category.id_comp]

private theorem triangle_target_transport {X S T : Scheme.{u}}
    (p : T ⟶ X) (q r : S ⟶ X) (a : T ⟶ S)
    (hq : a ≫ q = p) (hr : a ≫ r = p) (h : q = r)
    (B : AbelianSheaf.{u, u + 1} X) :
    (inverseImage a).map (eqToHom (congrArg (fun f => (inverseImage f).obj B) h)) ≫
      (pullbackTriangleIso p r a hr).inv.app B =
        (pullbackTriangleIso p q a hq).inv.app B := by
  exact map_transport_comp (inverseImage a)
    (fun f : S ⟶ X => (inverseImage f).obj B) (fun f => a ≫ f = p)
    ((inverseImage p).obj B) (fun f hf => (pullbackTriangleIso p f a hf).inv.app B)
    q r hq hr h

variable {I : Type u} [SmallCategory I] [IsFiltered I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (i : I)
  (r : (Functor.const I).obj (X.obj i) ⟶ X) (hr : r.app i = 𝟙 (X.obj i))
  (c : Cocone X) (hc : IsColimit c)
  [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop]
  (n : ℕ)

local instance : IsConnected I := IsFiltered.isConnected I

include hr hc

/-- Every original Hom between the pulled-back modeled bounded coefficients
comes from a genuine later-stage Hom, with its exact original triangle. -/
theorem exists_baseHom
    (A : BoundedPresentation.Coefficient (X.obj i).unop n)
    (hA : BoundedPresentation.finiteColimitStages (X.obj i).unop n A)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n)
    (γ : (inverseImage (c.ι.app i).unop).obj A.obj ⟶
      (inverseImage (c.ι.app i).unop).obj B.obj) :
    ∃ (a : Under i)
      (β : (inverseImage (X.map a.hom).unop).obj A.obj ⟶
        (inverseImage (X.map a.hom).unop).obj B.obj),
      (pullbackTriangleIso (c.ι.app i).unop (X.map a.hom).unop
          (c.ι.app a.right).unop (coneSquare X c a.hom)).hom.app A.obj ≫
          (inverseImage (c.ι.app a.right).unop).map β =
        γ ≫ (pullbackTriangleIso (c.ι.app i).unop (X.map a.hom).unop
          (c.ι.app a.right).unop (coneSquare X c a.hom)).hom.app B.obj := by
  let F := baseCoefficientSystem X i r n B
  let E := baseLimitCoefficientIso X i r hr c n B
  have hF : ∀ j, n • 𝟙 (F.obj j) = 0 := baseCoefficientSystem_killed X i r n B
  obtain ⟨a, β, hβ⟩ := exists_originalRightTailHom X c F hc n hF i A hA (γ ≫ E.inv)
  let q : (X.obj a.right).unop ⟶ (X.obj i).unop := (X.map a.hom).unop
  let p : c.pt.unop ⟶ (X.obj i).unop := (c.ι.app i).unop
  let p' : c.pt.unop ⟶ (X.obj a.right).unop := (c.ι.app a.right).unop
  let eB := baseStageIso X i r hr n B a
  let T := pullbackTriangleIso p q p' (coneSquare X c a.hom)
  have hins : colimit.ι (coneCoefficientFunctor X c F) a.right ≫ E.hom =
      (pullbackTriangleIso p (r.app a.right).unop p'
        (congrArg Quiver.Hom.unop (baseCone_fac X i r hr c a.right))).inv.app B.obj :=
    Stalk.ι_pullbackLimitCoefficientIso_hom X (Cone.mk (X.obj i) r) c (c.ι.app i)
      (baseCone_fac X i r hr c) B.obj a.right
  have htransport : (inverseImage p').map eB.hom ≫ T.inv.app B.obj =
      (pullbackTriangleIso p (r.app a.right).unop p'
        (congrArg Quiver.Hom.unop (baseCone_fac X i r hr c a.right))).inv.app B.obj :=
    triangle_target_transport p (r.app a.right).unop q p'
      (congrArg Quiver.Hom.unop (baseCone_fac X i r hr c a.right))
      (coneSquare X c a.hom) (congrArg Quiver.Hom.unop (baseCone_leg X i r hr a)) B.obj
  exact ⟨a, β ≫ eB.hom,
    AdjointStageHom.factorization_target_iso (inverseImage p') (T.hom.app A.obj) β eB (T.app B.obj)
      E (colimit.ι (coneCoefficientFunctor X c F) a.right) γ _ hins htransport hβ⟩

/-- Equality of the original limit pullbacks of two original model maps is
witnessed by equality after one actual later structural inverse image. -/
theorem baseHom_eventually_equal
    (A : BoundedPresentation.Coefficient (X.obj i).unop n)
    (hA : BoundedPresentation.finiteColimitStages (X.obj i).unop n A)
    (B : BoundedPresentation.Coefficient (X.obj i).unop n)
    (f g : A.obj ⟶ B.obj)
    (h : (inverseImage (c.ι.app i).unop).map f =
      (inverseImage (c.ι.app i).unop).map g) :
    ∃ a : Under i, (inverseImage (X.map a.hom).unop).map f =
      (inverseImage (X.map a.hom).unop).map g := by
  let F := baseCoefficientSystem X i r n B
  let E := baseLimitCoefficientIso X i r hr c n B
  let p : c.pt.unop ⟶ (X.obj i).unop := (c.ι.app i).unop
  have hF : ∀ j, n • 𝟙 (F.obj j) = 0 := baseCoefficientSystem_killed X i r n B
  exact AdjointStageHom.eventually_equal_of_units
    (Stages := fun a : Under i => AbelianSheaf.{u, u + 1} (X.obj a.right).unop)
    (inverseImage p) (directImage p) (inverseImageAdjunction p)
    (fun a => inverseImage (X.map a.hom).unop)
    (fun a => directImage (X.map a.hom).unop)
    (fun a => inverseImageAdjunction (X.map a.hom).unop)
    (diagramRightTail X F i) (diagramRightTailCocone X F c i)
    (baseRightTailUnit X i r hr n B)
    (fun {a b} t => baseRightTailUnit_naturality X i r hr n B t)
    ((directImage p).mapIso E)
    (baseRightTailUnit_point X i r hr c n B)
    (fun a => (directImage (X.map a.hom).unop).map (baseStageIso X i r hr n B a).hom)
    (baseRightTailUnit_value X i r hr n B)
    (fun a f g hfg => originalRightTailHom_eventually_equal X c F hc n hF
      i A hA a f g hfg)
    (Under.mk (𝟙 i)) f g h

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
