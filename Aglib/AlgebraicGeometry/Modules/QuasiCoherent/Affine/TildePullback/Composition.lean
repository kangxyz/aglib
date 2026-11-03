/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildePullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Sections.Map

/-!
# Tilde pullback composition at literal ring maps

These raw-map laws retain the native tilde comparison, the specified spectrum
triangle and the original scalar extension. The stable bundled-map provider is
imported without changes; only users of the additional raw laws import this leaf.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Functor
namespace AlgebraicGeometry.Scheme.Modules
variable {R S T : CommRingCat.{u}}

/-- Derive the complete native square for the given original Spec triangle. -/
theorem tildePullbackIso_ringHom_comp_hom_of_triangle (f : R →+* S) (g : S →+* T)
    (h : Spec.map (CommRingCat.ofHom (g.comp f) : R ⟶ T) =
      Spec.map (CommRingCat.ofHom g : S ⟶ T) ≫ Spec.map (CommRingCat.ofHom f : R ⟶ S)) :
    let φ : R ⟶ S := CommRingCat.ofHom f
    let ψ : S ⟶ T := CommRingCat.ofHom g
    let χ : R ⟶ T := CommRingCat.ofHom (g.comp f)
    whiskerLeft (tilde.functor R) ((pullbackCongr h).hom ≫
        (pullbackComp (Spec.map ψ) (Spec.map φ)).inv) ≫
      (associator _ _ _).inv ≫ whiskerRight (tildePullbackIso φ).hom (pullback (Spec.map ψ)) ≫
      (associator _ _ _).hom ≫
        whiskerLeft (ModuleCat.extendScalars f) (tildePullbackIso ψ).hom =
    (tildePullbackIso χ).hom ≫
      whiskerRight (ModuleCat.extendScalarsComp f g).hom (tilde.functor T) ≫
      (associator _ _ _).hom := by
  let φ : R ⟶ S := CommRingCat.ofHom f
  let ψ : S ⟶ T := CommRingCat.ofHom g
  let χ : R ⟶ T := CommRingCat.ofHom (g.comp f)
  change whiskerLeft (tilde.functor R) ((pullbackCongr h).hom ≫
      (pullbackComp (Spec.map ψ) (Spec.map φ)).inv) ≫
    (associator _ _ _).inv ≫ whiskerRight (tildePullbackIso φ).hom (pullback (Spec.map ψ)) ≫
    (associator _ _ _).hom ≫
      whiskerLeft (ModuleCat.extendScalars f) (tildePullbackIso ψ).hom =
    (tildePullbackIso χ).hom ≫
      whiskerRight (ModuleCat.extendScalarsComp f g).hom (tilde.functor T) ≫
      (associator _ _ _).hom
  apply (conjugateEquiv
    ((ModuleCat.extendRestrictScalarsAdj f).comp
      ((ModuleCat.extendRestrictScalarsAdj g).comp (tilde.adjunction (R := T))))
    ((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map χ)))).injective
  rw [← conjugateEquiv_comp _
      ((tilde.adjunction (R := R)).comp ((pullbackPushforwardAdjunction (Spec.map φ)).comp
        (pullbackPushforwardAdjunction (Spec.map ψ)))),
    ← conjugateEquiv_comp _
      (((tilde.adjunction (R := R)).comp (pullbackPushforwardAdjunction (Spec.map φ))).comp
        (pullbackPushforwardAdjunction (Spec.map ψ))),
    ← conjugateEquiv_comp _
      (((ModuleCat.extendRestrictScalarsAdj f).comp (tilde.adjunction (R := S))).comp
        (pullbackPushforwardAdjunction (Spec.map ψ))),
    ← conjugateEquiv_comp _
      ((ModuleCat.extendRestrictScalarsAdj f).comp
        ((tilde.adjunction (R := S)).comp (pullbackPushforwardAdjunction (Spec.map ψ))))]
  rw [← conjugateEquiv_comp _
      ((ModuleCat.extendRestrictScalarsAdj (g.comp f)).comp (tilde.adjunction (R := T))),
    ← conjugateEquiv_comp _
      (((ModuleCat.extendRestrictScalarsAdj f).comp
        (ModuleCat.extendRestrictScalarsAdj g)).comp (tilde.adjunction (R := T)))]
  rw [conjugateEquiv_whiskerLeft]
  erw [conjugateEquiv_tildePullbackIso_hom ψ]
  erw [conjugateEquiv_associator_hom (ModuleCat.extendRestrictScalarsAdj f)
    (tilde.adjunction (R := S)) (pullbackPushforwardAdjunction (Spec.map ψ))]
  rw [conjugateEquiv_whiskerRight]
  erw [conjugateEquiv_tildePullbackIso_hom φ]
  rw [conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft, ← conjugateEquiv_comp _
      (pullbackPushforwardAdjunction (Spec.map ψ ≫ Spec.map φ)), conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_pullbackCongr_hom]
  rw [conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight]
  erw [conjugateEquiv_tildePullbackIso_hom χ]
  rw [show conjugateEquiv ((ModuleCat.extendRestrictScalarsAdj f).comp
        (ModuleCat.extendRestrictScalarsAdj g)) (ModuleCat.extendRestrictScalarsAdj (g.comp f))
        (ModuleCat.extendScalarsComp f g).hom =
      (ModuleCat.restrictScalarsComp f g).inv from (conjugateEquiv _ _).apply_symm_apply _]
  ext M x
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine (congrFun (moduleSpecΓFunctor_map_coe (R := R)
    ((pushforwardCongr h).inv.app M)) _).trans ?_
  rw [pushforwardCongr_inv_app_app, eqToHom_op, eqToHom_map]
  rfl

/-- The complete native tilde composition square at the original raw scalar maps. -/
theorem tildePullbackIso_ringHom_comp_hom (f : R →+* S) (g : S →+* T) :
    let φ : R ⟶ S := CommRingCat.ofHom f
    let ψ : S ⟶ T := CommRingCat.ofHom g
    let χ : R ⟶ T := CommRingCat.ofHom (g.comp f)
    let hχ : Spec.map χ = Spec.map ψ ≫ Spec.map φ := Spec.map_comp φ ψ
    whiskerLeft (tilde.functor R) ((pullbackCongr hχ).hom ≫
        (pullbackComp (Spec.map ψ) (Spec.map φ)).inv) ≫
      (associator _ _ _).inv ≫ whiskerRight (tildePullbackIso φ).hom (pullback (Spec.map ψ)) ≫
      (associator _ _ _).hom ≫
        whiskerLeft (ModuleCat.extendScalars f) (tildePullbackIso ψ).hom =
    (tildePullbackIso χ).hom ≫
      whiskerRight (ModuleCat.extendScalarsComp f g).hom (tilde.functor T) ≫
      (associator _ _ _).hom := by
  exact tildePullbackIso_ringHom_comp_hom_of_triangle f g
    (Spec.map_comp (CommRingCat.ofHom f : R ⟶ S) (CommRingCat.ofHom g : S ⟶ T))

universe uC₀ uC₁ uC₂ uD₀ uD₁ uD₂ vC₀ vC₁ vC₂ vD₀ vD₁ vD₂

/-- Evaluate the complete comparison while its functors and transformations are variable. -/
private theorem tildeComparison_app_aux
    {C₀ : Type uC₀} {C₁ : Type uC₁} {C₂ : Type uC₂}
    {D₀ : Type uD₀} {D₁ : Type uD₁} {D₂ : Type uD₂}
    [Category.{vC₀} C₀] [Category.{vC₁} C₁] [Category.{vC₂} C₂]
    [Category.{vD₀} D₀] [Category.{vD₁} D₁] [Category.{vD₂} D₂]
    (L₀ : C₀ ⥤ D₀) (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
    (S : C₀ ⥤ C₁) (T : C₁ ⥤ C₂) (ST : C₀ ⥤ C₂)
    (A : D₀ ⥤ D₁) (B : D₁ ⥤ D₂) (AB AB' : D₀ ⥤ D₂)
    (α : L₀ ⋙ A ⟶ S ⋙ L₁) (β : L₁ ⋙ B ⟶ T ⋙ L₂)
    (γ : L₀ ⋙ AB ⟶ ST ⋙ L₂)
    (δ : AB ⟶ AB') (δ' : AB' ⟶ A ⋙ B) (ε : ST ⟶ S ⋙ T)
    (h : whiskerLeft L₀ (δ ≫ δ') ≫ (associator _ _ _).inv ≫
      whiskerRight α B ≫ (associator _ _ _).hom ≫ whiskerLeft S β =
      γ ≫ whiskerRight ε L₂ ≫ (associator _ _ _).hom) (P : C₀) :
    (δ.app (L₀.obj P) ≫ δ'.app (L₀.obj P)) ≫ 𝟙 _ ≫
        B.map (α.app P) ≫ 𝟙 _ ≫ β.app (S.obj P) =
      γ.app P ≫ L₂.map (ε.app P) ≫ 𝟙 _ := by
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj] using congr_app h P

universe uC vC

/-- Remove native identity components and transport the original first arrow. -/
private theorem tildeComponentChain_of_first_eq
    {C : Type uC} [Category.{vC} C]
    {X₀ X₁ X₂ X₃ X₄ Y : C}
    (d d₀ : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (c : X₃ ⟶ X₄) (r : X₀ ⟶ Y) (s : Y ⟶ X₄)
    (hd : d = d₀)
    (h : (d₀ ≫ a) ≫ 𝟙 X₂ ≫ b ≫ 𝟙 X₃ ≫ c = r ≫ s ≫ 𝟙 X₄) :
    d ≫ a ≫ b ≫ c = r ≫ s := by
  have h₀ : d₀ ≫ a ≫ b ≫ c = r ≫ s := by
    simpa only [Category.id_comp, Category.comp_id, Category.assoc] using h
  exact (congrArg (fun z : X₀ ⟶ X₁ => z ≫ a ≫ b ≫ c) hd).trans h₀

/-- Remove the same native identity components before specializing any object. -/
private theorem tildeComparison_app
    {C₀ : Type uC₀} {C₁ : Type uC₁} {C₂ : Type uC₂}
    {D₀ : Type uD₀} {D₁ : Type uD₁} {D₂ : Type uD₂}
    [Category.{vC₀} C₀] [Category.{vC₁} C₁] [Category.{vC₂} C₂]
    [Category.{vD₀} D₀] [Category.{vD₁} D₁] [Category.{vD₂} D₂]
    (L₀ : C₀ ⥤ D₀) (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)
    (S : C₀ ⥤ C₁) (T : C₁ ⥤ C₂) (ST : C₀ ⥤ C₂)
    (A : D₀ ⥤ D₁) (B : D₁ ⥤ D₂) (AB AB' : D₀ ⥤ D₂)
    (α : L₀ ⋙ A ⟶ S ⋙ L₁) (β : L₁ ⋙ B ⟶ T ⋙ L₂)
    (γ : L₀ ⋙ AB ⟶ ST ⋙ L₂)
    (δ : AB ⟶ AB') (δ' : AB' ⟶ A ⋙ B) (ε : ST ⟶ S ⋙ T)
    (h : whiskerLeft L₀ (δ ≫ δ') ≫ (associator _ _ _).inv ≫
      whiskerRight α B ≫ (associator _ _ _).hom ≫ whiskerLeft S β =
      γ ≫ whiskerRight ε L₂ ≫ (associator _ _ _).hom) (P : C₀) :
    δ.app (L₀.obj P) ≫ δ'.app (L₀.obj P) ≫
        B.map (α.app P) ≫ β.app (S.obj P) =
      γ.app P ≫ L₂.map (ε.app P) := by
  exact tildeComponentChain_of_first_eq (C := D₂)
    (δ.app (L₀.obj P)) (δ.app (L₀.obj P)) (δ'.app (L₀.obj P))
    (B.map (α.app P)) (β.app (S.obj P)) (γ.app P) (L₂.map (ε.app P)) rfl
    (tildeComparison_app_aux L₀ L₁ L₂ S T ST A B AB AB' α β γ δ δ' ε h P)

/-- Componentwise form of the raw tilde composition law, with the native associators
kept. The complete natural law is evaluated by the variable-functor component lemma
before specializing the original raw scalar maps. -/
theorem tildePullbackIso_ringHom_comp_hom_app_aux
    (f : R →+* S) (g : S →+* T) (N : ModuleCat.{u} R) :
    let φ : R ⟶ S := CommRingCat.ofHom f
    let ψ : S ⟶ T := CommRingCat.ofHom g
    let χ : R ⟶ T := CommRingCat.ofHom (g.comp f)
    let hχ : Spec.map χ = Spec.map ψ ≫ Spec.map φ := Spec.map_comp φ ψ
    ((pullbackCongr hχ).hom.app ((tilde.functor R).obj N) ≫
        (pullbackComp (Spec.map ψ) (Spec.map φ)).inv.app ((tilde.functor R).obj N)) ≫ 𝟙 _ ≫
        (pullback (Spec.map ψ)).map ((tildePullbackIso φ).hom.app N) ≫ 𝟙 _ ≫
        (tildePullbackIso ψ).hom.app ((ModuleCat.extendScalars f).obj N) =
      (tildePullbackIso χ).hom.app N ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp f g).hom.app N) ≫ 𝟙 _ := by
  dsimp only
  let φ : R ⟶ S := CommRingCat.ofHom f
  let ψ : S ⟶ T := CommRingCat.ofHom g
  let χ : R ⟶ T := CommRingCat.ofHom (g.comp f)
  let hχ : Spec.map χ = Spec.map ψ ≫ Spec.map φ := Spec.map_comp φ ψ
  exact tildeComparison_app_aux
    (tilde.functor R) (tilde.functor S) (tilde.functor T)
    (ModuleCat.extendScalars f) (ModuleCat.extendScalars g)
    (ModuleCat.extendScalars (g.comp f))
    (pullback (Spec.map φ)) (pullback (Spec.map ψ)) (pullback (Spec.map χ))
    (pullback (Spec.map ψ ≫ Spec.map φ))
    (tildePullbackIso φ).hom (tildePullbackIso ψ).hom (tildePullbackIso χ).hom
    (pullbackCongr hχ).hom
    (pullbackComp (Spec.map ψ) (Spec.map φ)).inv
    (ModuleCat.extendScalarsComp f g).hom
    (tildePullbackIso_ringHom_comp_hom f g) N

/-- The raw component comparison retains any proof of the original Spec triangle. -/
theorem tildePullbackIso_ringHom_comp_hom_app (f : R →+* S) (g : S →+* T)
    (h : Spec.map (CommRingCat.ofHom (g.comp f) : R ⟶ T) =
      Spec.map (CommRingCat.ofHom g : S ⟶ T) ≫ Spec.map (CommRingCat.ofHom f : R ⟶ S))
    (N : ModuleCat.{u} R) :
    let φ : R ⟶ S := CommRingCat.ofHom f
    let ψ : S ⟶ T := CommRingCat.ofHom g
    let χ : R ⟶ T := CommRingCat.ofHom (g.comp f)
    @Eq
      (@Quiver.Hom (Spec T).Modules inferInstance
        ((pullback (Spec.map χ)).obj ((tilde.functor R).obj N))
        ((tilde.functor T).obj
          ((ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj N))))
      ((pullbackCongr (X := Spec T) (Y := Spec R)
          (f := Spec.map χ) (g := Spec.map ψ ≫ Spec.map φ) h).hom.app
          ((tilde.functor R).obj N) ≫
        (pullbackComp (Spec.map ψ) (Spec.map φ)).inv.app ((tilde.functor R).obj N) ≫
        (pullback (Spec.map ψ)).map ((tildePullbackIso φ).hom.app N) ≫
        (tildePullbackIso ψ).hom.app ((ModuleCat.extendScalars f).obj N))
      ((tildePullbackIso χ).hom.app N ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp f g).hom.app N)) := by
  dsimp only
  let φ : R ⟶ S := CommRingCat.ofHom f
  let ψ : S ⟶ T := CommRingCat.ofHom g
  let χ : R ⟶ T := CommRingCat.ofHom (g.comp f)
  exact tildeComparison_app
    (tilde.functor R) (tilde.functor S) (tilde.functor T)
    (ModuleCat.extendScalars f) (ModuleCat.extendScalars g)
    (ModuleCat.extendScalars (g.comp f))
    (pullback (Spec.map φ)) (pullback (Spec.map ψ)) (pullback (Spec.map χ))
    (pullback (Spec.map ψ ≫ Spec.map φ))
    (tildePullbackIso φ).hom (tildePullbackIso ψ).hom (tildePullbackIso χ).hom
    (pullbackCongr (X := Spec T) (Y := Spec R)
      (f := Spec.map χ) (g := Spec.map ψ ≫ Spec.map φ) h).hom
    (pullbackComp (Spec.map ψ) (Spec.map φ)).inv
    (ModuleCat.extendScalarsComp f g).hom
    (tildePullbackIso_ringHom_comp_hom_of_triangle f g h) N

end AlgebraicGeometry.Scheme.Modules
