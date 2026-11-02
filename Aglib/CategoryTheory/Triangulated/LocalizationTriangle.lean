/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Localization and normalization of actual triangle functors

Three actual vertex comparisons make a triangle-valued functor invert the
localized morphisms. Native localization then constructs its lift and vertex
comparisons. Normalization retains specified first and second arrows and the
original connecting map. Source, localization and triangle categories have
independent universes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe uC vC uD vD uE vE

open CategoryTheory CategoryTheory.Pretriangulated

namespace CategoryTheory.Localization

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] [HasShift E ℤ]
  (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
  (T : C ⥤ Triangle E) (F₁ F₂ F₃ : D ⥤ E)
  (e₁ : T ⋙ Triangle.π₁ ≅ Q ⋙ F₁)
  (e₂ : T ⋙ Triangle.π₂ ≅ Q ⋙ F₂)
  (e₃ : T ⋙ Triangle.π₃ ≅ Q ⋙ F₃)

include e₁ e₂ e₃ in
/-- Actual vertex comparisons prove inversion of the localized morphisms. -/
theorem triangleFunctor_inverts : W.IsInvertedBy T := by
  intro X Y f hf
  let : IsIso (Q.map f) := Localization.inverts Q W f hf
  apply Triangle.isIso_of_isIsos
  · apply (NatIso.isIso_map_iff e₁ f).mpr
    change IsIso (F₁.map (Q.map f))
    infer_instance
  · apply (NatIso.isIso_map_iff e₂ f).mpr
    change IsIso (F₂.map (Q.map f))
    infer_instance
  · apply (NatIso.isIso_map_iff e₃ f).mpr
    change IsIso (F₃.map (Q.map f))
    infer_instance

/-- The native localization of the original triangle-valued functor. -/
def liftTriangleFunctor : D ⥤ Triangle E :=
  Localization.lift T (triangleFunctor_inverts Q W T F₁ F₂ F₃ e₁ e₂ e₃) Q

/-- The original native factorization of the localized triangle functor. -/
def liftTriangleFunctorFac :
    Q ⋙ liftTriangleFunctor Q W T F₁ F₂ F₃ e₁ e₂ e₃ ≅ T :=
  Localization.fac T (triangleFunctor_inverts Q W T F₁ F₂ F₃ e₁ e₂ e₃) Q

/-- Descend an actual vertex comparison, retaining the chosen localization. -/
def liftTriangleVertexIso (π : Triangle E ⥤ E) (F : D ⥤ E)
    (e : T ⋙ π ≅ Q ⋙ F) :
    liftTriangleFunctor Q W T F₁ F₂ F₃ e₁ e₂ e₃ ⋙ π ≅ F :=
  Localization.liftNatIso Q W _ _ _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (liftTriangleFunctorFac Q W T F₁ F₂ F₃ e₁ e₂ e₃) π ≪≫ e)

/-- The descended vertex comparison retains the whole original factorization. -/
theorem liftTriangleVertexIso_fac (π : Triangle E ⥤ E) (F : D ⥤ E)
    (e : T ⋙ π ≅ Q ⋙ F) :
    Functor.whiskerRight (liftTriangleFunctorFac Q W T F₁ F₂ F₃ e₁ e₂ e₃).hom π ≫ e.hom =
      (Functor.associator Q (liftTriangleFunctor Q W T F₁ F₂ F₃ e₁ e₂ e₃) π).hom ≫
        Functor.whiskerLeft Q
          (liftTriangleVertexIso Q W T F₁ F₂ F₃ e₁ e₂ e₃ π F e).hom := by
  apply NatTrans.ext
  funext X
  simp [liftTriangleVertexIso, Localization.liftNatIso, Localization.liftNatTrans_app,
    Localization.Lifting.iso]

/-- The component of the whole original vertex-factorization equation. -/
theorem liftTriangleVertexIso_hom_app (π : Triangle E ⥤ E) (F : D ⥤ E)
    (e : T ⋙ π ≅ Q ⋙ F) (X : C) :
    (liftTriangleVertexIso Q W T F₁ F₂ F₃ e₁ e₂ e₃ π F e).hom.app (Q.obj X) =
      π.map ((liftTriangleFunctorFac Q W T F₁ F₂ F₃ e₁ e₂ e₃).hom.app X) ≫ e.hom.app X := by
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] using
    (NatTrans.congr_app (liftTriangleVertexIso_fac Q W T F₁ F₂ F₃ e₁ e₂ e₃ π F e) X).symm

section Distinguished

variable [Limits.HasZeroObject E] [Preadditive E]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor E n).Additive] [Pretriangulated E]

/-- Distinguished source triangles remain distinguished after actual localization. -/
theorem liftTriangleFunctor_distinguished
    (hT : ∀ X, T.obj X ∈ distTriang E) (Y : D) :
    (liftTriangleFunctor Q W T F₁ F₂ F₃ e₁ e₂ e₃).obj Y ∈ distTriang E := by
  let : Q.EssSurj := Localization.essSurj Q W
  let X := Q.objPreimage Y
  let e : (liftTriangleFunctor Q W T F₁ F₂ F₃ e₁ e₂ e₃).obj Y ≅ T.obj X :=
    (liftTriangleFunctor Q W T F₁ F₂ F₃ e₁ e₂ e₃).mapIso (Q.objObjPreimageIso Y).symm ≪≫
      (liftTriangleFunctorFac Q W T F₁ F₂ F₃ e₁ e₂ e₃).app X
  exact isomorphic_distinguished _ (hT X) _ e

end Distinguished

end CategoryTheory.Localization

namespace CategoryTheory.Pretriangulated.Triangle

variable {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] [HasShift E ℤ]
  (T : D ⥤ Triangle E) {F₁ F₂ F₃ : D ⥤ E}
  (e₁ : T ⋙ Triangle.π₁ ≅ F₁) (e₂ : T ⋙ Triangle.π₂ ≅ F₂)
  (e₃ : T ⋙ Triangle.π₃ ≅ F₃) (a : F₁ ⟶ F₂) (b : F₂ ⟶ F₃)

/-- Normalize to specified first and second arrows, transporting the actual third arrow. -/
def normalizeFunctor : D ⥤ Triangle E :=
  Triangle.functorMk a b
    (e₃.inv ≫ Functor.whiskerLeft T Triangle.π₃Toπ₁ ≫
      Functor.whiskerRight e₁.hom (CategoryTheory.shiftFunctor E (1 : ℤ)))

/-- The normalized triangle has the original connecting arrow in the specified coordinates. -/
theorem normalizeFunctor_obj (X : D) :
    (normalizeFunctor T e₁ e₃ a b).obj X =
      Triangle.mk (a.app X) (b.app X)
        (e₃.inv.app X ≫ (T.obj X).mor₃ ≫
          (CategoryTheory.shiftFunctor E (1 : ℤ)).map (e₁.hom.app X)) := rfl

/-- Whole first and second comparison equations give the actual triangle isomorphism. -/
def normalizeFunctorIso
    (ha : Functor.whiskerLeft T Triangle.π₁Toπ₂ ≫ e₂.hom = e₁.hom ≫ a)
    (hb : Functor.whiskerLeft T Triangle.π₂Toπ₃ ≫ e₃.hom = e₂.hom ≫ b) :
    T ≅ normalizeFunctor T e₁ e₃ a b := by
  refine Triangle.functorIsoMk _ _ e₁ e₂ e₃ ha hb ?_
  apply NatTrans.ext
  funext X
  dsimp [normalizeFunctor, Triangle.functorMk]
  simp only [Iso.hom_inv_id_app_assoc]

/-- The normalized map is the original map in the specified triangle coordinates. -/
theorem normalizeFunctor_map_eq_original
    (ha : Functor.whiskerLeft T Triangle.π₁Toπ₂ ≫ e₂.hom = e₁.hom ≫ a)
    (hb : Functor.whiskerLeft T Triangle.π₂Toπ₃ ≫ e₃.hom = e₂.hom ≫ b)
    {X Y : D} (f : X ⟶ Y) :
    (normalizeFunctor T e₁ e₃ a b).map f =
      (normalizeFunctorIso T e₁ e₂ e₃ a b ha hb).inv.app X ≫ T.map f ≫
        (normalizeFunctorIso T e₁ e₂ e₃ a b ha hb).hom.app Y := by
  symm
  rw [(normalizeFunctorIso T e₁ e₂ e₃ a b ha hb).hom.naturality,
    ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

section Distinguished

variable [Limits.HasZeroObject E] [Preadditive E]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor E n).Additive] [Pretriangulated E]

/-- Specified-arrow normalization preserves actual distinguishedness. -/
theorem normalizeFunctor_distinguished
    (ha : Functor.whiskerLeft T Triangle.π₁Toπ₂ ≫ e₂.hom = e₁.hom ≫ a)
    (hb : Functor.whiskerLeft T Triangle.π₂Toπ₃ ≫ e₃.hom = e₂.hom ≫ b)
    (hT : ∀ X, T.obj X ∈ distTriang E) (X : D) :
    (normalizeFunctor T e₁ e₃ a b).obj X ∈ distTriang E :=
  isomorphic_distinguished _ (hT X) _ ((normalizeFunctorIso T e₁ e₂ e₃ a b ha hb).app X).symm

end Distinguished

end CategoryTheory.Pretriangulated.Triangle
