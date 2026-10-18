/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Restriction

/-!
# Original higher-image identity normalization and pasting

The original higher-image restriction over an identity base morphism is
normalized by the native identity-restriction isomorphism. These actual
maps paste on Cartesian open squares. All base schemes remain arbitrary;
no coefficient acyclicity or duality assertion is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

/-- The original three-factor normalization, with the base scheme held as an
abstract argument before any spectrum or polynomial model is substituted. -/
def identityHigherModelIso
    {X V Y : Scheme.{u}} (p : X ⟶ Y) (i : V ⟶ X) (q : V ⟶ Y)
    [IsOpenImmersion i] (H : IsPullback i q p (𝟙 Y)) (n : ℕ) :
    relativeHigherFunctor p n ≅ relativeHigherFunctor q n :=
  Functor.isoWhiskerLeft (relativeHigherFunctor p n)
      (restrictFunctorId (X := Y)).symm ≪≫
    relativeHigherRestrictionIso p i q (𝟙 Y) H n ≪≫
    Functor.isoWhiskerRight (restrictFunctorId (X := Y)) (relativeHigherFunctor q n)

/-- An actual module-level component formula, over an arbitrary base. -/
theorem identityHigherModelIso_hom
    {X V Y : Scheme.{u}} (p : X ⟶ Y) (i : V ⟶ X) (q : V ⟶ Y)
    [IsOpenImmersion i] (H : IsPullback i q p (𝟙 Y)) (n : ℕ) (N : Y.Modules) :
    let F₀ : Y.Modules ⥤ Y.Modules := relativeHigherFunctor p n
    let F₁ : Y.Modules ⥤ Y.Modules := relativeHigherFunctor q n
    let N₀ : Y.Modules := F₀.obj N
    let N₁ : Y.Modules := N₀.restrict (𝟙 Y)
    let N₂ : Y.Modules := F₁.obj (N.restrict (𝟙 Y))
    let N₃ : Y.Modules := F₁.obj N
    let d₀ : N₀ ⟶ N₁ := (restrictFunctorId (X := Y)).inv.app N₀
    let d₁ : N₁ ⟶ N₂ := relativeHigherRestrictionHom p i q (𝟙 Y) H n N
    let d₂ : N₂ ⟶ N₃ := F₁.map (X := N.restrict (𝟙 Y)) (Y := N)
      ((restrictFunctorId (X := Y)).hom.app N)
    @Eq (N₀ ⟶ N₃) ((identityHigherModelIso p i q H n).hom.app N)
      (@CategoryStruct.comp Y.Modules inferInstance N₀ N₁ N₃ d₀
        (@CategoryStruct.comp Y.Modules inferInstance N₁ N₂ N₃ d₁ d₂)) := by
  rfl

private theorem normalizeIdentityPasting
    {C : Type*} [Category* C] {A A' B B' M : C}
    (U : A' ≅ A) (V : B' ≅ B) (t : A ⟶ B) (a : A' ⟶ M) (b : M ⟶ B')
    (h : U.hom ≫ t ≫ V.inv = a ≫ b) :
    t = U.inv ≫ a ≫ b ≫ V.hom := by
  have h' := congrArg (fun z : A' ⟶ B' => U.inv ≫ z ≫ V.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h'

/-- The entire native identity-normalized pasting law, before substituting
canonical affine model morphisms or concrete spectrum carriers. -/
theorem identityHigherModelIso_open
    {X₀ X₁ V₀ V₁ Y₀ Y₁ : Scheme.{u}}
    (p₀ : X₀ ⟶ Y₀) (p₁ : X₁ ⟶ Y₁) (q₀ : V₀ ⟶ Y₀) (q₁ : V₁ ⟶ Y₁)
    (i : X₁ ⟶ X₀) (j : Y₁ ⟶ Y₀) (e₀ : V₀ ⟶ X₀) (e₁ : V₁ ⟶ X₁) (g : V₁ ⟶ V₀)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion e₀]
    [IsOpenImmersion e₁] [IsOpenImmersion g]
    (H : IsPullback i p₁ p₀ j) (H₀ : IsPullback e₀ q₀ p₀ (𝟙 Y₀))
    (H₁ : IsPullback e₁ q₁ p₁ (𝟙 Y₁)) (G : IsPullback g q₁ q₀ j)
    (w : e₁ ≫ i = g ≫ e₀) (n : ℕ) (N : Y₀.Modules) :
    (relativeHigherRestrictionIso p₀ i p₁ j H n).hom.app N ≫
        (identityHigherModelIso p₁ e₁ q₁ H₁ n).hom.app (N.restrict j) =
      (Modules.restrictFunctor j).map
          (X := (relativeHigherFunctor p₀ n).obj N)
          (Y := (relativeHigherFunctor q₀ n).obj N)
          ((identityHigherModelIso p₀ e₀ q₀ H₀ n).hom.app N) ≫
        (relativeHigherRestrictionIso q₀ g q₁ j G n).hom.app N := by
  let F₀ := relativeHigherFunctor p₀ n
  let F₂ := relativeHigherFunctor q₁ n
  let J := Modules.restrictFunctor j
  let uA := restrictFunctorId (X := Y₀)
  let uB := restrictFunctorId (X := Y₁)
  let α := (relativeHigherRestrictionIso p₀ i p₁ j H n).hom.app N
  let β := relativeHigherRestrictionIso q₀ g q₁ j G n
  let m₀ := relativeHigherRestrictionIso p₀ e₀ q₀ (𝟙 Y₀) H₀ n
  let m₁ := relativeHigherRestrictionIso p₁ e₁ q₁ (𝟙 Y₁) H₁ n
  let HT : IsPullback (g ≫ e₀) q₁ p₀ j := by
    simpa only [Category.comp_id] using G.paste_horiz H₀
  let T := relativeHigherRestrictionIso p₀ (g ≫ e₀) q₁ j HT n
  have h₁ := relativeHigherRestrictionIso_comp p₀ p₁ q₁ i j e₁ (𝟙 Y₁) H H₁
    (H₁.paste_horiz H) n N
  have h₂ := relativeHigherRestrictionIso_comp p₀ q₀ q₁ e₀ (𝟙 Y₀) g j H₀ G
    (G.paste_horiz H₀) n N
  rw [relativeHigherRestrictionIso_congr p₀ q₁ (e₁ ≫ i) (g ≫ e₀)
    (𝟙 Y₁ ≫ j) j (H₁.paste_horiz H) HT w (Category.id_comp j) n N] at h₁
  rw [relativeHigherRestrictionIso_congr p₀ q₁ (g ≫ e₀) (g ≫ e₀)
    (j ≫ 𝟙 Y₀) j (G.paste_horiz H₀) HT rfl (Category.comp_id j) n N] at h₂
  have hL := congrArg F₂.map (restrictCompLeftUnit_inv j N)
  have hR := congrArg F₂.map (restrictCompRightUnit_inv j N)
  simp only [Functor.map_comp] at hL hR
  simp only [Category.assoc] at h₁ h₂
  rw [restrictCompLeftUnit_hom_assoc, hL] at h₁
  rw [restrictCompRightUnit_hom_assoc, hR] at h₂
  let U₀ := uB.app ((F₀.obj N).restrict j)
  let U₁ := F₂.mapIso (uB.app (N.restrict j))
  let V₀ := J.mapIso (uA.app (F₀.obj N))
  let V₁ := F₂.mapIso (J.mapIso (uA.app N))
  change U₀.hom ≫ T.hom.app N ≫ U₁.inv =
    (Modules.restrictFunctor (𝟙 Y₁)).map α ≫ m₁.hom.app (N.restrict j) at h₁
  change V₀.hom ≫ T.hom.app N ≫ V₁.inv =
    J.map (m₀.hom.app N) ≫ β.hom.app (N.restrict (𝟙 Y₀)) at h₂
  have h1n := normalizeIdentityPasting U₀ U₁ (T.hom.app N)
    ((Modules.restrictFunctor (𝟙 Y₁)).map α) (m₁.hom.app (N.restrict j)) h₁
  have h2n := normalizeIdentityPasting V₀ V₁ (T.hom.app N)
    (J.map (m₀.hom.app N)) (β.hom.app (N.restrict (𝟙 Y₀))) h₂
  have hη : α ≫ uB.inv.app ((relativeHigherFunctor p₁ n).obj (N.restrict j)) =
      U₀.inv ≫ (Modules.restrictFunctor (𝟙 Y₁)).map α := uB.inv.naturality α
  have hν := β.hom.naturality (X := N.restrict (𝟙 Y₀)) (Y := N) (uA.hom.app N)
  change J.map ((relativeHigherFunctor q₀ n).map (uA.hom.app N)) ≫ β.hom.app N =
    β.hom.app (N.restrict (𝟙 Y₀)) ≫ F₂.map (J.map (uA.hom.app N)) at hν
  change T.hom.app N = V₀.inv ≫ J.map (m₀.hom.app N) ≫
    β.hom.app (N.restrict (𝟙 Y₀)) ≫ F₂.map (J.map (uA.hom.app N)) at h2n
  rw [← reassoc_of% hη] at h1n
  rw [← hν] at h2n
  simpa only [identityHigherModelIso, U₀, U₁, V₀, V₁,
    F₀, F₂, J, uA, uB, α, β, m₀, m₁, Functor.comp_obj, Functor.id_obj,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc] using
      h1n.symm.trans h2n

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
