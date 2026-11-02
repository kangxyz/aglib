/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # Original exchange coherence over independently sized categories -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA uB uA' vA vB vA'

variable {A : Type uA} {B : Type uB} {A' : Type uA'} [Category.{vA} A] [Category.{vB} B]
  [Category.{vA'} A']
  {I : B ⥤ B} {F F₀ F₁ : A ⥤ B} {G₀ G₁ : A' ⥤ B} {V : A ⥤ A'}

/-- Normalize an original target identity functor without changing its map. -/
def identityFunctorNormalizer (F : A ⥤ B) (i : I ≅ 𝟭 B) : F ⋙ I ≅ F :=
  Functor.isoWhiskerLeft F i ≪≫ Functor.rightUnitor F

/-- Original identity normalization is natural in the specified comparison. -/
theorem identityFunctorNormalizer_naturality (c : F₀ ≅ F₁) (i : I ≅ 𝟭 B) :
    Functor.isoWhiskerRight c I ≪≫ identityFunctorNormalizer F₁ i =
      identityFunctorNormalizer F₀ i ≪≫ c := by
  apply Iso.ext
  ext X
  simp only [identityFunctorNormalizer, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  calc
    _ = I.map (c.hom.app X) ≫ i.hom.app (F₁.obj X) :=
      congrArg (fun z => I.map (c.hom.app X) ≫ z)
        (Category.comp_id (i.hom.app (F₁.obj X)))
    _ = i.hom.app (F₀.obj X) ≫ c.hom.app X := by
      simpa only [Functor.id_map] using i.hom.naturality (c.hom.app X)
    _ = _ := congrArg (fun z => z ≫ c.hom.app X)
      (Category.comp_id (i.hom.app (F₀.obj X))).symm

/-- Postcomposition retains the already proved original identity normalization. -/
theorem identityBaseChange_postcomp
    (β : F ⋙ I ≅ V ⋙ G₀) (i : I ≅ 𝟭 B) (ψ : F ≅ V ⋙ G₀) (c : G₀ ≅ G₁)
    (h : β = Functor.isoWhiskerLeft F i ≪≫ Functor.rightUnitor F ≪≫ ψ) :
    β ≪≫ Functor.isoWhiskerLeft V c =
      identityFunctorNormalizer F i ≪≫ (ψ ≪≫ Functor.isoWhiskerLeft V c) := by
  simp only [h, identityFunctorNormalizer, Iso.trans_assoc]

/-- The actual base-change model equation and actual identity normalization
prove independence of the separately defined identity-specific source transport. -/
theorem identitySourceTransport_model
    (β₀ : F₀ ⋙ I ≅ V ⋙ G₀) (β₁ : F₁ ⋙ I ≅ V ⋙ G₁)
    (ψ₀ : F₀ ≅ V ⋙ G₀) (ψ₁ : F₁ ≅ V ⋙ G₁)
    (c : F₀ ≅ F₁) (d : G₀ ≅ G₁) (i : I ≅ 𝟭 B)
    (hmodel : Functor.isoWhiskerRight c I ≪≫ β₁ =
      β₀ ≪≫ Functor.isoWhiskerLeft V d)
    (h₀ : β₀ = identityFunctorNormalizer F₀ i ≪≫ ψ₀)
    (h₁ : β₁ = identityFunctorNormalizer F₁ i ≪≫ ψ₁) :
    c ≪≫ ψ₁ = ψ₀ ≪≫ Functor.isoWhiskerLeft V d := by
  rw [h₀, h₁, ← Iso.trans_assoc, identityFunctorNormalizer_naturality,
    Iso.trans_assoc, Iso.trans_assoc] at hmodel
  apply Iso.ext
  have hh := congrArg Iso.hom hmodel
  simp only [Iso.trans_hom] at hh
  exact (cancel_epi (identityFunctorNormalizer F₀ i).hom).mp hh

end CategoryTheory
