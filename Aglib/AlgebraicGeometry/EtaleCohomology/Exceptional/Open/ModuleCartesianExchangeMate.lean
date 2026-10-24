/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleExchangeSourcePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleEtaleExchangeMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleCartesianBaseChange

/-! # The original mate of an arbitrary Cartesian module exchange -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

private theorem replace_two_parameters {A B : Sort*} (P : A → B → Prop)
    {a a' : A} {b b' : B} (ha : a = a') (hb : b = b') (hp : P a' b') : P a b := by
  cases ha
  cases hb
  exact hp

private theorem source_cancel {C : Type*} [Category C]
    {A B D E F G : C} (x : A ⟶ B) (a : B ⟶ D) (b : D ⟶ E)
    (c : E ⟶ G) (d : B ⟶ F) (e : F ⟶ E) (z : A ⟶ G)
    (t : G ⟶ E) (r : B ⟶ G)
    (hr : r = a ≫ b ≫ c) (hn : a ≫ b = d ≫ e)
    (hs : x ≫ d ≫ e = z ≫ t) (hc : t ≫ c = 𝟙 G) : x ≫ r = z := by
  calc
    x ≫ r = (x ≫ d ≫ e) ≫ c := by
      rw [hr, ← Category.assoc a, hn]
      simp only [Category.assoc]
    _ = (z ≫ t) ≫ c := congrArg (fun k => k ≫ c) hs
    _ = z := by rw [Category.assoc, hc, Category.comp_id]

/-- Source pasting with the given, rather than renamed, factor maps. -/
@[reassoc]
theorem moduleBaseChangeMap_source_transport {V P U Y X : Scheme.{u}}
    (Λ : Type (u + 1)) [Ring Λ] (p : P ⟶ U) (q : P ⟶ Y)
    (j : U ⟶ X) (f : Y ⟶ X) (h : p ≫ j = q ≫ f) (e : V ⟶ P)
    (g : V ⟶ U) (i : V ⟶ Y) (hg : e ≫ p = g) (hi : e ≫ q = i)
    (he : g ≫ j = i ≫ f) (M : ModuleSheaf Y Λ) :
    (moduleBaseChangeMap Λ f g j i he).app M ≫
      (eqToIso (congrArg (fun k => moduleDirectImage k Λ) hg.symm) ≪≫
        moduleDirectImageCompIso Λ p e).hom.app ((moduleInverseImage i Λ).obj M) ≫
      (moduleDirectImage p Λ).map ((moduleDirectImage e Λ).map
        ((moduleSourceInverseImageIso Λ q e i hi).hom.app M)) =
    (moduleBaseChangeMap Λ f p j q h).app M ≫
      (moduleDirectImage p Λ).map
        ((moduleInverseImageAdjunction e Λ).unit.app ((moduleInverseImage q Λ).obj M)) := by
  subst g
  subst i
  simpa only [moduleSourceInverseImageIso, eqToIso_refl, Iso.trans_hom,
    NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    moduleBaseChangeMap_source_comp Λ p q j f h e he M

variable {V U Y X : Scheme.{u}} (g : V ⟶ U) (i : V ⟶ Y) (j : U ⟶ X) (f : Y ⟶ X)
  [Etale i] [Etale j] (h : IsPullback g i j f) (Λ : Type (u + 1)) [Ring Λ]

omit [Etale i] [Etale j] in
/-- The Cartesian right comparison on an object retains the original canonical-source unit. -/
theorem moduleCartesianRightIso_hom_app (M : ModuleSheaf Y Λ) :
    (moduleCartesianRightIso g i j f h Λ).hom.app M =
      (moduleDirectImage g Λ).map ((moduleCartesianInverseImageIso g i j f h Λ).hom.app M) ≫
        (moduleCartesianDirectImageIso g i j f h Λ).hom.app
          ((moduleInverseImage h.isoPullback.hom Λ).obj
            ((moduleInverseImage (pullback.snd j f) Λ).obj M)) ≫
        (moduleDirectImage (pullback.fst j f) Λ).map
          ((moduleInverseImageUnitIsoOfIso Λ h.isoPullback).inv.app
            ((moduleInverseImage (pullback.snd j f) Λ).obj M)) := by
  simp only [moduleCartesianRightIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Iso.symm_hom,
    Category.id_comp, Functor.comp_obj]
  exact congrArg (fun z =>
    (moduleDirectImage g Λ).map ((moduleCartesianInverseImageIso g i j f h Λ).hom.app M) ≫
      (moduleCartesianDirectImageIso g i j f h Λ).hom.app
        ((moduleInverseImage h.isoPullback.hom Λ).obj
          ((moduleInverseImage (pullback.snd j f) Λ).obj M)) ≫ z)
    (Category.comp_id ((moduleDirectImage (pullback.fst j f) Λ).map
      ((moduleInverseImageUnitIsoOfIso Λ h.isoPullback).inv.app
        ((moduleInverseImage (pullback.snd j f) Λ).obj M))))

omit [Etale i] [Etale j] in
private theorem cartesian_direct_whole :
    moduleCartesianDirectImageIso g i j f h Λ =
      eqToIso (congrArg (fun k => moduleDirectImage k Λ) h.isoPullback_hom_fst.symm) ≪≫
        moduleDirectImageCompIso Λ (pullback.fst j f) h.isoPullback.hom := rfl

omit [Etale i] [Etale j] in
private theorem cartesian_inverse_whole :
    moduleCartesianInverseImageIso g i j f h Λ =
      moduleSourceInverseImageIso Λ (pullback.snd j f) h.isoPullback.hom i
        h.isoPullback_hom_snd := rfl

omit [Etale i] [Etale j] in
private theorem cartesian_source_component (M : ModuleSheaf Y Λ) :
    (moduleBaseChangeMap Λ f g j i h.w).app M ≫
      (moduleCartesianDirectImageIso g i j f h Λ).hom.app
        ((moduleInverseImage i Λ).obj M) ≫
      (moduleDirectImage (pullback.fst j f) Λ).map
        ((moduleDirectImage h.isoPullback.hom Λ).map
          ((moduleCartesianInverseImageIso g i j f h Λ).hom.app M)) =
    (moduleBaseChangeMap Λ f (pullback.fst j f) j (pullback.snd j f)
      pullback.condition).app M ≫
      (moduleDirectImage (pullback.fst j f) Λ).map
        ((moduleInverseImageAdjunction h.isoPullback.hom Λ).unit.app
          ((moduleInverseImage (pullback.snd j f) Λ).obj M)) := by
  exact replace_two_parameters (fun
    (d : moduleDirectImage g Λ ≅ moduleDirectImage h.isoPullback.hom Λ ⋙
      moduleDirectImage (pullback.fst j f) Λ)
    (k : moduleInverseImage i Λ ≅ moduleInverseImage (pullback.snd j f) Λ ⋙
      moduleInverseImage h.isoPullback.hom Λ) =>
    (moduleBaseChangeMap Λ f g j i h.w).app M ≫
      d.hom.app ((moduleInverseImage i Λ).obj M) ≫
      (moduleDirectImage (pullback.fst j f) Λ).map
        ((moduleDirectImage h.isoPullback.hom Λ).map (k.hom.app M)) =
    (moduleBaseChangeMap Λ f (pullback.fst j f) j (pullback.snd j f)
      pullback.condition).app M ≫
      (moduleDirectImage (pullback.fst j f) Λ).map
        ((moduleInverseImageAdjunction h.isoPullback.hom Λ).unit.app
          ((moduleInverseImage (pullback.snd j f) Λ).obj M)))
    (cartesian_direct_whole g i j f h Λ) (cartesian_inverse_whole g i j f h Λ)
    (moduleBaseChangeMap_source_transport Λ (pullback.fst j f)
      (pullback.snd j f) j f pullback.condition h.isoPullback.hom g i
      h.isoPullback_hom_fst h.isoPullback_hom_snd h.w M)

omit [Etale i] [Etale j] in
private theorem cartesian_unit_component (M : ModuleSheaf Y Λ) :
    (moduleDirectImage (pullback.fst j f) Λ).map
        ((moduleInverseImageAdjunction h.isoPullback.hom Λ).unit.app
          ((moduleInverseImage (pullback.snd j f) Λ).obj M)) ≫
      (moduleDirectImage (pullback.fst j f) Λ).map
        ((moduleInverseImageUnitIsoOfIso Λ h.isoPullback).inv.app
          ((moduleInverseImage (pullback.snd j f) Λ).obj M)) = 𝟙 _ :=
  ((moduleDirectImage (pullback.fst j f) Λ).mapIso
    ((moduleInverseImageUnitIsoOfIso Λ h.isoPullback).app
      ((moduleInverseImage (pullback.snd j f) Λ).obj M))).hom_inv_id

omit [Etale i] [Etale j] in
private theorem cartesian_original_map (M : ModuleSheaf Y Λ) :
    (moduleBaseChangeMap Λ f g j i h.w).app M ≫
      (moduleCartesianRightIso g i j f h Λ).hom.app M =
    (moduleBaseChangeMap Λ f (pullback.fst j f) j (pullback.snd j f)
      pullback.condition).app M := by
  exact source_cancel _ _ _ _ _ _ _ _ _
    (moduleCartesianRightIso_hom_app g i j f h Λ M)
    ((moduleCartesianDirectImageIso g i j f h Λ).hom.naturality
      ((moduleCartesianInverseImageIso g i j f h Λ).hom.app M))
    (cartesian_source_component g i j f h Λ M)
    (cartesian_unit_component g i j f h Λ M)

omit [Etale i] in
/-- The given Cartesian exchange is the original pullback mate under source transport. -/
@[reassoc]
theorem moduleCartesianExchange_original (M : ModuleSheaf Y Λ) :
    (moduleBaseChangeMap Λ f g j i h.w).app M ≫
      (moduleCartesianRightIso g i j f h Λ).hom.app M =
    (moduleEtaleBaseChangeIso f j Λ).hom.app M :=
  (cartesian_original_map g i j f h Λ M).trans
    (congrArg (fun z => z.app M) (moduleEtaleBaseChangeIso_hom f j Λ)).symm

omit [Etale i] in
/-- The accepted arbitrary Cartesian exchange is exactly the original adjunction mate. -/
theorem moduleCartesianExchangeIso_hom :
    (moduleCartesianExchangeIso g i j f h Λ).hom =
      moduleBaseChangeMap Λ f g j i h.w := by
  apply (cancel_mono (moduleCartesianRightIso g i j f h Λ).hom).1
  apply NatTrans.ext
  funext M
  simp only [moduleCartesianExchangeIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  exact (moduleCartesianExchange_original g i j f h Λ M).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
