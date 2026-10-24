/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Cohomology
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Native dual homology and original derived Hom

The original class comparison descends as a natural isomorphism of additive
functors. Linearity is then proved over the original source module functor,
using its native scalar action and source naturality. The coefficient, model,
localization and shift maps are unchanged. Native additive ULifts only reconcile
carrier universes and disappear from the public linear equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

attribute [local instance] CategoryTheory.Linear.opposite

/-- The original additive Hom functor, with literal source precomposition. -/
def CategoryTheory.homAdditiveFunctor
    {C : Type*} [Category.{w} C] [Preadditive C] (Y : C) : Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj X := AddCommGrpCat.of (X.unop ⟶ Y)
  map f := AddCommGrpCat.ofHom (Preadditive.leftComp Y f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro f
    exact Category.id_comp f
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro h
    exact Category.assoc _ _ h

/-- Native source scalars act by the same scalar on the original Hom group. -/
theorem CategoryTheory.homAdditiveFunctor_smul_id
    {C : Type*} [Category.{w} C] [Preadditive C]
    {A : Type*} [CommRing A] [Linear A C] (Y : C) (X : Cᵒᵖ) (a : A)
    (f : X.unop ⟶ Y) :
    (homAdditiveFunctor Y).map (a • 𝟙 X) f = a • f := by
  change (a • 𝟙 X.unop) ≫ f = a • f
  rw [Linear.smul_comp, Category.id_comp]

/-- Postcompose original Hom groups with the raw components of the given natural isomorphism. -/
def CategoryTheory.NatIso.homPostcompAddEquiv
    {C D : Type*} [Category* C] [Category* D] [Preadditive D]
    {F G : C ⥤ D} (e : F ≅ G) (X : C) (U : D) :
    (U ⟶ F.obj X) ≃+ (U ⟶ G.obj X) where
  toFun f := f ≫ e.hom.app X
  invFun f := f ≫ e.inv.app X
  left_inv f := by
    change (f ≫ e.hom.app X) ≫ e.inv.app X = f
    rw [Category.assoc, e.hom_inv_id_app, Category.comp_id]
  right_inv f := by
    change (f ≫ e.inv.app X) ≫ e.hom.app X = f
    rw [Category.assoc, e.inv_hom_id_app, Category.comp_id]
  map_add' f g := Preadditive.add_comp _ _ _ f g (e.hom.app X)

private theorem nativeClassIso_naturality
    {C : Type*} [Category* C] {A : Type*} [Ring A]
    (F : C ⥤ ModuleCat.{v} A) (G : C ⥤ AddCommGrpCat.{v})
    (e : F ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat ≅ G)
    {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    ModuleCat.natIsoAddEquiv F G e Y ((F.map f).hom x) =
      G.map f (ModuleCat.natIsoAddEquiv F G e X x) :=
  ConcreteCategory.congr_hom (e.hom.naturality f) x

/-- Unlift the native Hom component and postcompose with the original inverse target isomorphism. -/
def ModuleCat.liftedHomIsoValue
    {C D : Type*} [Category* C] [Category.{w} D] [Preadditive D]
    {A : Type*} [Ring A] (F : Cᵒᵖ ⥤ ModuleCat.{v} A) (L : C ⥤ D)
    {Y Y' : D} (s : Y ≅ Y')
    (E : F ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙
        AddCommGrpCat.uliftFunctor.{w, v}) ≅
      L.op ⋙ (CategoryTheory.homAdditiveFunctor Y' ⋙ AddCommGrpCat.uliftFunctor.{v, w}))
    (X : C) (x : F.obj (op X)) : L.obj X ⟶ Y :=
  (show L.obj X ⟶ Y' from ((E.hom.app (op X)).hom (ULift.up x)).down) ≫ s.inv

private theorem liftedHomIsoValue_naturality
    {C D : Type*} [Category* C] [Category.{w} D] [Preadditive D]
    {A : Type*} [Ring A] (F : Cᵒᵖ ⥤ ModuleCat.{v} A) (L : C ⥤ D)
    {Y Y' : D} (s : Y ≅ Y')
    (E : F ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙
        AddCommGrpCat.uliftFunctor.{w, v}) ≅
      L.op ⋙ (CategoryTheory.homAdditiveFunctor Y' ⋙ AddCommGrpCat.uliftFunctor.{v, w}))
    {X Z : C} (f : X ⟶ Z) (x : F.obj (op Z)) :
    ModuleCat.liftedHomIsoValue F L s E X ((F.map f.op).hom x) =
      L.map f ≫ ModuleCat.liftedHomIsoValue F L s E Z x := by
  have h : (show L.obj X ⟶ Y' from ((E.hom.app (op X)).hom
        (ULift.up ((F.map f.op).hom x))).down) =
      L.map f ≫ (show L.obj Z ⟶ Y' from ((E.hom.app (op Z)).hom (ULift.up x)).down) :=
    congrArg ULift.down (ConcreteCategory.congr_hom (E.hom.naturality f.op) (ULift.up x))
  change (show L.obj X ⟶ Y' from ((E.hom.app (op X)).hom
      (ULift.up ((F.map f.op).hom x))).down) ≫ s.inv =
    L.map f ≫ ((show L.obj Z ⟶ Y' from
      ((E.hom.app (op Z)).hom (ULift.up x)).down) ≫ s.inv)
  exact (congrArg (fun t : L.obj X ⟶ Y' => t ≫ s.inv) h).trans
    (Category.assoc _ _ _)

/-- Lift the original additive class comparison without constructing another module action. -/
def ModuleCat.liftedClassNatIso
    {C : Type*} [Category* C] {A : Type*} [Ring A]
    (F : C ⥤ ModuleCat.{v} A) (G : C ⥤ AddCommGrpCat.{v})
    (e : F ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat ≅ G)
    (H : C ⥤ AddCommGrpCat.{w}) (d : ∀ X, G.obj X ≃+ H.obj X)
    (hn : ∀ {X Y} (f : X ⟶ Y) y, d Y (G.map f y) = H.map f (d X y)) :
    F ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{w, v}) ≅
      H ⋙ AddCommGrpCat.uliftFunctor.{v, w} :=
  NatIso.ofComponents (fun X =>
    ((AddEquiv.ulift : ULift.{w} (F.obj X) ≃+ F.obj X).trans
      ((ModuleCat.natIsoAddEquivTrans F G e X (d X)).trans
        (AddEquiv.ulift : ULift.{v} (H.obj X) ≃+ H.obj X).symm)).toAddCommGrpIso)
    (by
      intro X Y f
      apply ConcreteCategory.hom_ext
      intro x
      apply ULift.ext
      exact (congrArg (d Y) (nativeClassIso_naturality F G e f x.down)).trans
        (hn f (ModuleCat.natIsoAddEquiv F G e X x.down)))

/-- The lifted class comparison retains its explicit original forward function. -/
theorem ModuleCat.liftedClassNatIso_hom_apply
    {C : Type*} [Category* C] {A : Type*} [Ring A]
    (F : C ⥤ ModuleCat.{v} A) (G : C ⥤ AddCommGrpCat.{v})
    (e : F ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat ≅ G)
    (H : C ⥤ AddCommGrpCat.{w}) (d : ∀ X, G.obj X ≃+ H.obj X)
    (hn : ∀ {X Y} (f : X ⟶ Y) y, d Y (G.map f y) = H.map f (d X y))
    (X : C) (x : F.obj X) :
    (((ModuleCat.liftedClassNatIso F G e H d hn).hom.app X).hom (ULift.up x)).down =
      d X (ModuleCat.natIsoAddEquiv F G e X x) := rfl

/-- Remove the two additive universe lifts from a complete original comparison. -/
def ModuleCat.liftedAddIsoEquiv
    {C : Type*} [Category* C] {A : Type*} [Ring A]
    (F : C ⥤ ModuleCat.{v} A) (G : C ⥤ AddCommGrpCat.{w})
    (e : F ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{w, v}) ≅
      G ⋙ AddCommGrpCat.uliftFunctor.{v, w}) (X : C) : F.obj X ≃+ G.obj X :=
  (AddEquiv.ulift : ULift.{w} (F.obj X) ≃+ F.obj X).symm.trans
    ((e.app X).addCommGroupIsoToAddEquiv.trans
      (AddEquiv.ulift : ULift.{v} (G.obj X) ≃+ G.obj X))

private theorem liftedAddIsoEquiv_naturality
    {C : Type*} [Category* C] {A : Type*} [Ring A]
    (F : C ⥤ ModuleCat.{v} A) (G : C ⥤ AddCommGrpCat.{w})
    (e : F ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{w, v}) ≅
      G ⋙ AddCommGrpCat.uliftFunctor.{v, w})
    {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    ModuleCat.liftedAddIsoEquiv F G e Y ((F.map f).hom x) =
      G.map f (ModuleCat.liftedAddIsoEquiv F G e X x) :=
  congrArg ULift.down (ConcreteCategory.congr_hom (e.hom.naturality f) (ULift.up x))

/-- Native source linearity upgrades the original additive comparison, generically. -/
def ModuleCat.linearEquivOfLiftedAddIso
    {C : Type*} [Category* C] [Preadditive C]
    {A : Type*} [CommRing A] [Linear A C]
    (F : C ⥤ ModuleCat.{v} A) [F.Linear A] (G : C ⥤ AddCommGrpCat.{w})
    (e : F ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{w, v}) ≅
      G ⋙ AddCommGrpCat.uliftFunctor.{v, w}) (X : C)
    {T : Type*} [AddCommGroup T] [Module A T] (d : G.obj X ≃+ T)
    (hd : ∀ (a : A) (y : G.obj X), d (G.map (a • 𝟙 X) y) = a • d y) :
    F.obj X ≃ₗ[A] T :=
  { (ModuleCat.liftedAddIsoEquiv F G e X).trans d with
    map_smul' a x := by
      have h := liftedAddIsoEquiv_naturality F G e (a • 𝟙 X) x
      rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id] at h
      change ModuleCat.liftedAddIsoEquiv F G e X (a • x) =
        G.map (a • 𝟙 X) (ModuleCat.liftedAddIsoEquiv F G e X x) at h
      exact (congrArg d h).trans (hd a (ModuleCat.liftedAddIsoEquiv F G e X x)) }

/-- The native linear structure does not alter the original forward function. -/
theorem ModuleCat.linearEquivOfLiftedAddIso_apply
    {C : Type*} [Category* C] [Preadditive C]
    {A : Type*} [CommRing A] [Linear A C]
    (F : C ⥤ ModuleCat.{v} A) [F.Linear A] (G : C ⥤ AddCommGrpCat.{w})
    (e : F ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{w, v}) ≅
      G ⋙ AddCommGrpCat.uliftFunctor.{v, w}) (X : C)
    {T : Type*} [AddCommGroup T] [Module A T] (d : G.obj X ≃+ T)
    (hd : ∀ (a : A) (y : G.obj X), d (G.map (a • 𝟙 X) y) = a • d y) (x : F.obj X) :
    ModuleCat.linearEquivOfLiftedAddIso F G e X d hd x =
      d (((e.hom.app X).hom (ULift.up x)).down) := rfl

private theorem lifted_class_linear_constructor_apply
    {C : Type*} [Category* C] [Preadditive C]
    {A : Type*} [CommRing A] [Linear A C]
    (F : C ⥤ ModuleCat.{v} A) [F.Linear A] (G : C ⥤ AddCommGrpCat.{v})
    (e : F ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat ≅ G)
    (H : C ⥤ AddCommGrpCat.{w}) (d : ∀ X, G.obj X ≃+ H.obj X)
    (hn : ∀ {X Y} (f : X ⟶ Y) y, d Y (G.map f y) = H.map f (d X y))
    (X : C) {T : Type*} [AddCommGroup T] [Module A T] (d₀ : G.obj X ≃+ T)
    (h₀ : ∀ (a : A) (y : G.obj X), d₀ (G.map (a • 𝟙 X) y) = a • d₀ y)
    (p : T → H.obj X) (hp : ∀ y, d X y = p (d₀ y)) (x : F.obj X) :
    (((ModuleCat.liftedClassNatIso F G e H d hn).hom.app X).hom (ULift.up x)).down =
      p (ModuleCat.natIsoAddEquivTransLinear F G e X d₀ h₀ x) := by
  rw [ModuleCat.liftedClassNatIso_hom_apply]
  exact hp (ModuleCat.natIsoAddEquiv F G e X x)

private theorem linear_constructor_coe_eq_lifted_class_value
    {C D : Type*} [Category* C] [Preadditive C] [Category.{w} D] [Preadditive D]
    {A : Type*} [CommRing A] [Linear A C] [Linear A D]
    (F : Cᵒᵖ ⥤ ModuleCat.{v} A) [F.Linear A] (G : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (e : F ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat ≅ G) (L : C ⥤ D)
    {Y Y' : D} (s : Y ≅ Y')
    (d : ∀ Z, G.obj Z ≃+ (L.op ⋙ CategoryTheory.homAdditiveFunctor Y').obj Z)
    (hn : ∀ {X Z} (f : X ⟶ Z) y,
      d Z (G.map f y) = (L.op ⋙ CategoryTheory.homAdditiveFunctor Y').map f (d X y))
    (X : C) (d₀ : G.obj (op X) ≃+ (L.obj X ⟶ Y))
    (h₀ : ∀ (a : A) (y : G.obj (op X)),
      d₀ (G.map (a • 𝟙 (op X)) y) = a • d₀ y)
    (hp : ∀ y, d (op X) y = d₀ y ≫ s.hom) :
    (ModuleCat.natIsoAddEquivTransLinear F G e (op X) d₀ h₀ :
      F.obj (op X) → (L.obj X ⟶ Y)) =
        ModuleCat.liftedHomIsoValue F L s
          (ModuleCat.liftedClassNatIso F G e
              (L.op ⋙ CategoryTheory.homAdditiveFunctor Y') d hn ≪≫
            Functor.associator L.op (CategoryTheory.homAdditiveFunctor Y')
              AddCommGrpCat.uliftFunctor.{v, w}) X := by
  funext x
  let E := ModuleCat.liftedClassNatIso F G e
    (L.op ⋙ CategoryTheory.homAdditiveFunctor Y') d hn
  change ModuleCat.natIsoAddEquivTransLinear F G e (op X) d₀ h₀ x =
    (((E.hom.app (op X) ≫ 𝟙 _).hom (ULift.up x)).down) ≫ s.inv
  rw [Category.comp_id]
  have h := lifted_class_linear_constructor_apply F G e
    (L.op ⋙ CategoryTheory.homAdditiveFunctor Y') d hn (op X) d₀ h₀
    (fun f => f ≫ s.hom) hp x
  rw [h, Category.assoc, s.hom_inv_id, Category.comp_id]

private theorem lifted_linear_constructor_model_apply
    {C D : Type*} [Category* C] [Category* D] [Preadditive D]
    {A : Type*} [CommRing A] [Linear A D]
    (L : C ⥤ D) (F : D ⥤ ModuleCat.{v} A) [F.Linear A]
    (G : D ⥤ AddCommGrpCat.{w})
    (E : F ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙
        AddCommGrpCat.uliftFunctor.{w, v}) ≅ G ⋙ AddCommGrpCat.uliftFunctor.{v, w})
    (M : C ⥤ ModuleCat.{v} A) (m : L ⋙ F ≅ M)
    (c : M ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙
        AddCommGrpCat.uliftFunctor.{w, v}) ≅ L ⋙ (G ⋙ AddCommGrpCat.uliftFunctor.{v, w}))
    (X : C)
    (h : E.hom.app (L.obj X) =
      (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{w, v}).map
        (m.hom.app X) ≫ c.hom.app X)
    {T : Type*} [AddCommGroup T] [Module A T] (d : G.obj (L.obj X) ≃+ T)
    (hd : ∀ (a : A) (y : G.obj (L.obj X)),
      d (G.map (a • 𝟙 (L.obj X)) y) = a • d y) (x : F.obj (L.obj X)) :
    ModuleCat.linearEquivOfLiftedAddIso F G E (L.obj X) d hd x =
      d (((c.hom.app X).hom (ULift.up ((m.hom.app X).hom x))).down) := by
  rw [ModuleCat.linearEquivOfLiftedAddIso_apply, h]
  rfl

private theorem lifted_linear_constructor_model_class_apply
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {A : Type*} [CommRing A] [Linear A C] [Linear A D]
    (L : C ⥤ D) (F : D ⥤ ModuleCat.{v} A) [F.Linear A]
    (G : D ⥤ AddCommGrpCat.{w})
    (E : F ⋙ (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙
        AddCommGrpCat.uliftFunctor.{w, v}) ≅ G ⋙ AddCommGrpCat.uliftFunctor.{v, w})
    (F₀ : C ⥤ ModuleCat.{v} A) [F₀.Linear A] (G₀ : C ⥤ AddCommGrpCat.{v})
    (e₀ : F₀ ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat ≅ G₀)
    (d : ∀ X, G₀.obj X ≃+ (L ⋙ G).obj X)
    (hn : ∀ {X Y} (f : X ⟶ Y) y, d Y (G₀.map f y) = (L ⋙ G).map f (d X y))
    (m : L ⋙ F ≅ F₀) (X : C)
    (h : E.hom.app (L.obj X) =
      (forget₂ (ModuleCat.{v} A) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{w, v}).map
        (m.hom.app X) ≫
          ((ModuleCat.liftedClassNatIso F₀ G₀ e₀ (L ⋙ G) d hn ≪≫
            Functor.associator L G AddCommGrpCat.uliftFunctor.{v, w}).hom.app X))
    {T : Type*} [AddCommGroup T] [Module A T] (b : G.obj (L.obj X) ≃+ T)
    (hb : ∀ (a : A) (y : G.obj (L.obj X)),
      b (G.map (a • 𝟙 (L.obj X)) y) = a • b y)
    {P : Type*} [AddCommGroup P] [Module A P] (d₀ : G₀.obj X ≃+ P)
    (h₀ : ∀ (a : A) (y : G₀.obj X), d₀ (G₀.map (a • 𝟙 X) y) = a • d₀ y)
    (p : P → (L ⋙ G).obj X) (hp : ∀ y, d X y = p (d₀ y))
    (x : F.obj (L.obj X)) :
    ModuleCat.linearEquivOfLiftedAddIso F G E (L.obj X) b hb x =
      b (p (ModuleCat.natIsoAddEquivTransLinear F₀ G₀ e₀ X d₀ h₀
        ((m.hom.app X).hom x))) := by
  let c := ModuleCat.liftedClassNatIso F₀ G₀ e₀ (L ⋙ G) d hn ≪≫
    Functor.associator L G AddCommGrpCat.uliftFunctor.{v, w}
  have h₁ := lifted_linear_constructor_model_apply L F G E F₀ m c X h b hb x
  have h₂ : (((c.hom.app X).hom (ULift.up ((m.hom.app X).hom x))).down) =
      p (ModuleCat.natIsoAddEquivTransLinear F₀ G₀ e₀ X d₀ h₀
        ((m.hom.app X).hom x)) := by
    change (((ModuleCat.liftedClassNatIso F₀ G₀ e₀ (L ⋙ G) d hn).hom.app X ≫ 𝟙 _).hom
      (ULift.up ((m.hom.app X).hom x))).down = _
    rw [Category.comp_id]
    exact lifted_class_linear_constructor_apply F₀ G₀ e₀ (L ⋙ G) d hn X d₀ h₀ p hp _
  exact h₁.trans (congrArg b h₂)

private theorem module_function_model_inverse
    {R : Type*} [Ring R] {M N : ModuleCat.{v} R} {T : Type*}
    (E : M ≅ N) (p : M → T) (q : N → T)
    (h : ∀ x, p x = q (E.hom.hom x)) (x : N) :
    p (E.inv.hom x) = q x := by
  have hx : E.hom.hom (E.inv.hom x) = x :=
    ConcreteCategory.congr_hom E.inv_hom_id x
  exact (h _).trans (congrArg q hx)

namespace CochainComplex.HomComplex

variable {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (J : CochainComplex (ModuleCat.{max u v} A) ℤ) [J.IsKInjective] (n : ℤ)

/-- The literal original dual followed by native homology, with one shared carrier presentation. -/
abbrev derivedDualHomologyFunctor :
    (DerivedCategory (ModuleCat.{max u v} A))ᵒᵖ ⥤ ModuleCat.{max u v} A :=
  derivedDual J ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n

/-- The original dual and homology factorizations on actual chain representatives. -/
def derivedDualHomologyModelNatIso :
    DerivedCategory.Q.op ⋙ derivedDualHomologyFunctor J n ≅
      moduleHomologyFunctor J n := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n
  let B := moduleComplexFunctor A J
  let E := derivedDualFactors J
  let P := DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) n
  refine NatIso.ofComponents (fun K => H.mapIso (E.app K) ≪≫ P.app (B.obj K)) ?_
  intro K L f
  have hE := congrArg H.map (E.hom.naturality f)
  simp only [CategoryTheory.Functor.map_comp] at hE
  have hP := P.hom.naturality (B.map f)
  change H.map ((derivedDual J).map (DerivedCategory.Q.op.map f)) ≫ H.map (E.hom.app L) =
    H.map (E.hom.app K) ≫ H.map (DerivedCategory.Q.map (B.map f)) at hE
  change H.map (DerivedCategory.Q.map (B.map f)) ≫ P.hom.app (B.obj L) =
    P.hom.app (B.obj K) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A) (.up ℤ) n).map (B.map f) at hP
  change H.map ((derivedDual J).map (DerivedCategory.Q.op.map f)) ≫ H.map (E.hom.app L) ≫
      P.hom.app (B.obj L) =
    (H.map (E.hom.app K) ≫ P.hom.app (B.obj K)) ≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A) (.up ℤ) n).map (B.map f)
  rw [← Category.assoc, hE, Category.assoc, hP]
  simp only [Category.assoc]

/-- The model comparison is homology of the original dual factor followed by
the original localization/homology factor. -/
theorem derivedDualHomologyModelNatIso_hom_app
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (derivedDualHomologyModelNatIso J n).hom.app (op K) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
          ((derivedDualFactors J).hom.app (op K)) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) n).hom.app
          (moduleComplex A K J) := rfl


local instance originalQ_op_linear :
    (DerivedCategory.Q (C := ModuleCat.{max u v} A)).op.Linear A where
  map_smul {X Y} f a := by
    apply Quiver.Hom.unop_inj
    change DerivedCategory.Q.map (a • (show Y.unop ⟶ X.unop from f.unop)) =
      a • DerivedCategory.Q.map f.unop
    exact DerivedCategory.Q.map_smul a f.unop

/-- The native homology action descends from the original chain Hom functor. -/
instance derivedDualHomologyFunctor_linear : (derivedDualHomologyFunctor J n).Linear A := by
  let L := (DerivedCategory.Q (C := ModuleCat.{max u v} A)).op
  let W := (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (.up ℤ)).op
  let : Localization.Lifting L W (moduleHomologyFunctor J n)
      (derivedDualHomologyFunctor J n) := ⟨derivedDualHomologyModelNatIso J n⟩
  exact (Localization.functor_linear_iff L W A (moduleHomologyFunctor J n)
    (derivedDualHomologyFunctor J n)).mp inferInstance

/-- Original dual homology after forgetting only scalar data and lifting the carrier universe. -/
def derivedDualHomologyLiftedFunctor :
    (DerivedCategory (ModuleCat.{max u v} A))ᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  derivedDualHomologyFunctor J n ⋙
    (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat ⋙
      AddCommGrpCat.uliftFunctor.{w, max u v})

/-- The original derived Hom groups, retaining literal source precomposition. -/
def derivedDualHomAddFunctor :
    (DerivedCategory (ModuleCat.{max u v} A))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  CategoryTheory.homAdditiveFunctor ((DerivedCategory.Q.obj J)⟦n⟧)

/-- The same original Hom groups in the common additive carrier universe. -/
def derivedDualHomLiftedFunctor :
    (DerivedCategory (ModuleCat.{max u v} A))ᵒᵖ ⥤ AddCommGrpCat.{max u v w} :=
  derivedDualHomAddFunctor J n ⋙ AddCommGrpCat.uliftFunctor.{max u v, w}

/-- Original class localization, followed by the raw native Q-shift component. -/
def derivedDualCohomologyShiftAddEquiv (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    CohomologyClass K J n ≃+ (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj J)⟦n⟧) :=
  (cohomologyDerivedEquiv K J n).trans
    (CategoryTheory.NatIso.homPostcompAddEquiv (DerivedCategory.Q.commShiftIso n) J
      (DerivedCategory.Q.obj K))

theorem derivedDualCohomologyShiftAddEquiv_smul
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (a : A) (x : CohomologyClass K J n) :
    derivedDualCohomologyShiftAddEquiv J n K (cohomologyPrecomp (a • 𝟙 K) J n x) =
      a • derivedDualCohomologyShiftAddEquiv J n K x := by
  change cohomologyDerivedEquiv K J n (cohomologyPrecomp (a • 𝟙 K) J n x) ≫ _ =
    a • (cohomologyDerivedEquiv K J n x ≫ _)
  rw [cohomologyDerivedEquiv_precomp_smul_id, Linear.smul_comp]

theorem derivedDualCohomologyShiftAddEquiv_precomp
    {K L : CochainComplex (ModuleCat.{max u v} A) ℤ} (f : K ⟶ L)
    (x : CohomologyClass L J n) :
    derivedDualCohomologyShiftAddEquiv J n K (cohomologyPrecomp f J n x) =
      DerivedCategory.Q.map f ≫ derivedDualCohomologyShiftAddEquiv J n L x := by
  change cohomologyDerivedEquiv K J n (cohomologyPrecomp f J n x) ≫ _ =
    DerivedCategory.Q.map f ≫ (cohomologyDerivedEquiv L J n x ≫ _)
  rw [cohomologyDerivedEquiv_precomp, Category.assoc]

/-- The same original class map on the literal additive-functor carriers. -/
def derivedDualCohomologyClassComparison
    (K : (CochainComplex (ModuleCat.{max u v} A) ℤ)ᵒᵖ) :
    (cohomologyClassFunctor J n).obj K ≃+
      (DerivedCategory.Q.op ⋙ derivedDualHomAddFunctor J n).obj K :=
  derivedDualCohomologyShiftAddEquiv J n K.unop

/-- The same original source scalar law is retained on the additive-functor carriers. -/
theorem derivedDualCohomologyClassComparison_smul
    (K : (CochainComplex (ModuleCat.{max u v} A) ℤ)ᵒᵖ) (a : A)
    (x : (cohomologyClassFunctor J n).obj K) :
    derivedDualCohomologyClassComparison J n K
        ((cohomologyClassFunctor J n).map (a • 𝟙 K) x) =
      a • (show DerivedCategory.Q.obj K.unop ⟶ (DerivedCategory.Q.obj J)⟦n⟧ from
        derivedDualCohomologyClassComparison J n K x) :=
  derivedDualCohomologyShiftAddEquiv_smul J n K.unop a x

/-- Every original chain arrow retains its original class-precomposition equation. -/
theorem derivedDualCohomologyClassComparison_naturality
    {K L : (CochainComplex (ModuleCat.{max u v} A) ℤ)ᵒᵖ} (f : K ⟶ L)
    (x : (cohomologyClassFunctor J n).obj K) :
    derivedDualCohomologyClassComparison J n L ((cohomologyClassFunctor J n).map f x) =
      (DerivedCategory.Q.op ⋙ derivedDualHomAddFunctor J n).map f
        (derivedDualCohomologyClassComparison J n K x) :=
  derivedDualCohomologyShiftAddEquiv_precomp J n f.unop x

/-- The original complete class comparison, lifted only as additive functors. -/
def derivedDualHomologyChainNatIso :
    moduleHomologyFunctor J n ⋙
        (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat ⋙
          AddCommGrpCat.uliftFunctor.{w, max u v}) ≅
      DerivedCategory.Q.op ⋙ derivedDualHomLiftedFunctor J n :=
  ModuleCat.liftedClassNatIso
      (moduleHomologyFunctor J n) (cohomologyClassFunctor J n) (moduleHomologyClassesNatIso J n)
      (DerivedCategory.Q.op ⋙ derivedDualHomAddFunctor J n)
      (derivedDualCohomologyClassComparison J n)
      (derivedDualCohomologyClassComparison_naturality J n) ≪≫
    Functor.associator DerivedCategory.Q.op (derivedDualHomAddFunctor J n)
      AddCommGrpCat.uliftFunctor.{max u v, w}

/-- The lifted chain comparison evaluates to its original class/localization/Q-shift map. -/
theorem derivedDualHomologyChainNatIso_hom_app_apply
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (x : (moduleComplex A K J).homology n) :
    (((derivedDualHomologyChainNatIso J n).hom.app (op K)).hom (ULift.up x)).down =
      moduleHomologyDerivedLinearEquiv K J n x ≫
        (DerivedCategory.Q.commShiftIso n).hom.app J := by
  let E := ModuleCat.liftedClassNatIso
    (moduleHomologyFunctor J n) (cohomologyClassFunctor J n) (moduleHomologyClassesNatIso J n)
    (DerivedCategory.Q.op ⋙ derivedDualHomAddFunctor J n)
    (derivedDualCohomologyClassComparison J n)
    (derivedDualCohomologyClassComparison_naturality J n)
  change ((E.hom.app (op K) ≫ 𝟙 _).hom (ULift.up x)).down = _
  rw [Category.comp_id]
  exact lifted_class_linear_constructor_apply
    (moduleHomologyFunctor J n) (cohomologyClassFunctor J n) (moduleHomologyClassesNatIso J n)
    (DerivedCategory.Q.op ⋙ derivedDualHomAddFunctor J n)
    (derivedDualCohomologyClassComparison J n)
    (derivedDualCohomologyClassComparison_naturality J n) (op K)
    (cohomologyDerivedEquiv K J n) (cohomologyDerivedEquiv_precomp_smul_id K J n)
    (fun f => f ≫ (DerivedCategory.Q.commShiftIso n).hom.app J) (fun _ => rfl) x

/-- The native chain component followed by the inverse of the same original Q-shift.
This function fixes the source and target before applying a concrete comparison. -/
def moduleHomologyDerivedValue (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (moduleComplex A K J).homology n →
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (J⟦n⟧)) :=
  ModuleCat.liftedHomIsoValue (moduleHomologyFunctor J n)
    (DerivedCategory.Q (C := ModuleCat.{max u v} A))
    ((DerivedCategory.Q.commShiftIso n).app J) (derivedDualHomologyChainNatIso J n) K

/-- The compact native component function is exactly the original linear comparison.
Its original class, localization and scalar action are thereby retained. -/
theorem moduleHomologyDerivedLinearEquiv_coe
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (moduleHomologyDerivedLinearEquiv K J n : (moduleComplex A K J).homology n →
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (J⟦n⟧))) =
        moduleHomologyDerivedValue J n K := by
  exact linear_constructor_coe_eq_lifted_class_value
    (moduleHomologyFunctor J n) (cohomologyClassFunctor J n) (moduleHomologyClassesNatIso J n)
    (DerivedCategory.Q (C := ModuleCat.{max u v} A)) ((DerivedCategory.Q.commShiftIso n).app J)
    (derivedDualCohomologyClassComparison J n)
    (derivedDualCohomologyClassComparison_naturality J n) K
    (cohomologyDerivedEquiv K J n) (cohomologyDerivedEquiv_precomp_smul_id K J n)
    (fun _ => rfl)

/-- The original module comparison keeps every original chain precomposition map. -/
theorem moduleHomologyDerivedLinearEquiv_precomp
    {K L : CochainComplex (ModuleCat.{max u v} A) ℤ} (f : K ⟶ L)
    (x : (moduleComplex A L J).homology n) :
    moduleHomologyDerivedLinearEquiv K J n
        ((HomologicalComplex.homologyMap (precomp A f J) n).hom x) =
      DerivedCategory.Q.map f ≫ moduleHomologyDerivedLinearEquiv L J n x := by
  have h := liftedHomIsoValue_naturality (moduleHomologyFunctor J n)
    (DerivedCategory.Q (C := ModuleCat.{max u v} A))
    ((DerivedCategory.Q.commShiftIso n).app J) (derivedDualHomologyChainNatIso J n) f x
  change moduleHomologyDerivedValue J n K
      ((HomologicalComplex.homologyMap (precomp A f J) n).hom x) =
    DerivedCategory.Q.map f ≫ moduleHomologyDerivedValue J n L x at h
  rw [← moduleHomologyDerivedLinearEquiv_coe J n K,
    ← moduleHomologyDerivedLinearEquiv_coe J n L] at h
  exact h

/-- The original model map followed by the complete original additive class comparison. -/
def derivedDualHomologyPrelocalizedIso :
    DerivedCategory.Q.op ⋙ derivedDualHomologyLiftedFunctor J n ≅
      DerivedCategory.Q.op ⋙ derivedDualHomLiftedFunctor J n := by
  let V := forget₂ (ModuleCat.{max u v} A) AddCommGrpCat ⋙
    AddCommGrpCat.uliftFunctor.{w, max u v}
  exact (Functor.associator DerivedCategory.Q.op (derivedDualHomologyFunctor J n) V).symm ≪≫
    Functor.isoWhiskerRight (derivedDualHomologyModelNatIso J n) V ≪≫
    derivedDualHomologyChainNatIso J n

/-- Descent retains the whole original additive natural isomorphism. -/
def derivedDualHomologyNatIso :
    derivedDualHomologyLiftedFunctor J n ≅ derivedDualHomLiftedFunctor J n :=
  Localization.liftNatIso DerivedCategory.Q.op
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (.up ℤ)).op
    (DerivedCategory.Q.op ⋙ derivedDualHomologyLiftedFunctor J n)
    (DerivedCategory.Q.op ⋙ derivedDualHomLiftedFunctor J n)
    (derivedDualHomologyLiftedFunctor J n) (derivedDualHomLiftedFunctor J n)
    (derivedDualHomologyPrelocalizedIso J n)

/-- The original descended component on Q(K) is exactly its prelocalized component. -/
theorem derivedDualHomologyNatIso_hom_app_Q
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (derivedDualHomologyNatIso J n).hom.app (op (DerivedCategory.Q.obj K)) =
      (derivedDualHomologyPrelocalizedIso J n).hom.app (op K) := by
  let L := (DerivedCategory.Q (C := ModuleCat.{max u v} A)).op
  let W := (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (.up ℤ)).op
  let F := derivedDualHomologyLiftedFunctor J n
  let G := derivedDualHomLiftedFunctor J n
  let E := derivedDualHomologyPrelocalizedIso J n
  change (Localization.liftNatTrans L W (L ⋙ F) (L ⋙ G) F G E.hom).app (L.obj (op K)) = _
  rw [Localization.liftNatTrans_app]
  change (𝟙 _) ≫ E.hom.app (op K) ≫ (𝟙 _) = _
  rw [Category.id_comp, Category.comp_id]

/-- The native A-linear equivalence on every actual derived source.
Its action is not transported. -/
def derivedDualHomologyLinearEquiv (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (derivedDualHomologyFunctor J n).obj (op X) ≃ₗ[A]
      (X ⟶ (DerivedCategory.Q.obj J)⟦n⟧) := by
  let d : (derivedDualHomAddFunctor J n).obj (op X) ≃+
      (X ⟶ (DerivedCategory.Q.obj J)⟦n⟧) := AddEquiv.refl _
  exact ModuleCat.linearEquivOfLiftedAddIso (derivedDualHomologyFunctor J n)
    (derivedDualHomAddFunctor J n) (derivedDualHomologyNatIso J n) (op X)
    d (CategoryTheory.homAdditiveFunctor_smul_id
      ((DerivedCategory.Q.obj J)⟦n⟧) (op X))

/-- The actual forward map is the unlifted original additive component. -/
theorem derivedDualHomologyLinearEquiv_apply
    (X : DerivedCategory (ModuleCat.{max u v} A))
    (x : (derivedDualHomologyFunctor J n).obj (op X)) :
    derivedDualHomologyLinearEquiv J n X x =
      (((derivedDualHomologyNatIso J n).hom.app (op X)).hom (ULift.up x)).down := by
  let d : (derivedDualHomAddFunctor J n).obj (op X) ≃+
      (X ⟶ (DerivedCategory.Q.obj J)⟦n⟧) := AddEquiv.refl _
  exact ModuleCat.linearEquivOfLiftedAddIso_apply (derivedDualHomologyFunctor J n)
    (derivedDualHomAddFunctor J n) (derivedDualHomologyNatIso J n) (op X)
    d (CategoryTheory.homAdditiveFunctor_smul_id
      ((DerivedCategory.Q.obj J)⟦n⟧) (op X)) x

/-- Every original derived arrow, including the original unit and boundary,
acts by precomposition. -/
theorem derivedDualHomologyLinearEquiv_naturality
    {X Y : DerivedCategory (ModuleCat.{max u v} A)} (f : X ⟶ Y)
    (x : (derivedDualHomologyFunctor J n).obj (op Y)) :
    derivedDualHomologyLinearEquiv J n X
        (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
          ((derivedDual J).map f.op)).hom x) =
      f ≫ derivedDualHomologyLinearEquiv J n Y x := by
  have h := ConcreteCategory.congr_hom
    ((derivedDualHomologyNatIso J n).hom.naturality f.op) (ULift.up x)
  exact congrArg ULift.down h

/-- The prelocalized map retains its original model component before the original class map. -/
theorem derivedDualHomologyPrelocalizedIso_hom_app
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (derivedDualHomologyPrelocalizedIso J n).hom.app (op K) =
      (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat ⋙
          AddCommGrpCat.uliftFunctor.{w, max u v}).map
          ((derivedDualHomologyModelNatIso J n).hom.app (op K)) ≫
        (derivedDualHomologyChainNatIso J n).hom.app (op K) := by
  change (𝟙 _) ≫ _ ≫ _ = _
  exact (Category.id_comp _).trans (by rfl)

/-- On an original chain source, the forward map retains model, classes,
localization and Q-shift. -/
theorem derivedDualHomologyLinearEquiv_Q
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (x : (derivedDualHomologyFunctor J n).obj (DerivedCategory.Q.op.obj (op K))) :
    let m : (derivedDualHomologyFunctor J n).obj (DerivedCategory.Q.op.obj (op K)) →ₗ[A]
        (moduleHomologyFunctor J n).obj (op K) :=
      ((derivedDualHomologyModelNatIso J n).hom.app (op K)).hom
    derivedDualHomologyLinearEquiv J n (DerivedCategory.Q.obj K) x =
      moduleHomologyDerivedLinearEquiv K J n (m x) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app J := by
  let d : (derivedDualHomAddFunctor J n).obj (DerivedCategory.Q.op.obj (op K)) ≃+
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj J)⟦n⟧) := AddEquiv.refl _
  have h := (derivedDualHomologyNatIso_hom_app_Q J n K).trans
    (derivedDualHomologyPrelocalizedIso_hom_app J n K)
  exact lifted_linear_constructor_model_class_apply DerivedCategory.Q.op
    (derivedDualHomologyFunctor J n) (derivedDualHomAddFunctor J n)
    (derivedDualHomologyNatIso J n) (moduleHomologyFunctor J n)
    (cohomologyClassFunctor J n) (moduleHomologyClassesNatIso J n)
    (derivedDualCohomologyClassComparison J n)
    (derivedDualCohomologyClassComparison_naturality J n) (derivedDualHomologyModelNatIso J n)
    (op K) h d (CategoryTheory.homAdditiveFunctor_smul_id
      ((DerivedCategory.Q.obj J)⟦n⟧) (op (DerivedCategory.Q.obj K)))
    (cohomologyDerivedEquiv K J n) (cohomologyDerivedEquiv_precomp_smul_id K J n)
    (fun f => f ≫ (DerivedCategory.Q.commShiftIso n).hom.app J) (fun _ => rfl) x

/-- The normalization displays the original dual factor and homology factor separately. -/
theorem derivedDualHomologyLinearEquiv_Q_factors
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (x : (derivedDualHomologyFunctor J n).obj (DerivedCategory.Q.op.obj (op K))) :
    derivedDualHomologyLinearEquiv J n (DerivedCategory.Q.obj K) x =
      moduleHomologyDerivedLinearEquiv K J n
          (((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) n).hom.app
            (moduleComplex A K J)).hom
            (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
              ((derivedDualFactors J).hom.app (op K))).hom x)) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app J := by
  rw [derivedDualHomologyLinearEquiv_Q, derivedDualHomologyModelNatIso_hom_app]
  rfl

/-- Any supplied original representative is transported by its actual inverse. -/
theorem derivedDualHomologyLinearEquiv_iso
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    {X : DerivedCategory (ModuleCat.{max u v} A)} (e : DerivedCategory.Q.obj K ≅ X)
    (x : (derivedDualHomologyFunctor J n).obj (op X)) :
    derivedDualHomologyLinearEquiv J n X x =
      e.inv ≫ derivedDualHomologyLinearEquiv J n (DerivedCategory.Q.obj K)
        (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
          ((derivedDual J).map e.hom.op)).hom x) := by
  rw [derivedDualHomologyLinearEquiv_naturality, Iso.inv_hom_id_assoc]

/-- Every original Hom cocycle retains its literal localized shifted chain map. -/
theorem derivedDualHomologyLinearEquiv_cocycle
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (z : Cocycle K J n) :
    let x : (moduleHomologyFunctor J n).obj (op K) := moduleCocycleClass K J n z
    let e : (moduleHomologyFunctor J n).obj (op K) →ₗ[A]
        (derivedDualHomologyFunctor J n).obj (DerivedCategory.Q.op.obj (op K)) :=
      ((derivedDualHomologyModelNatIso J n).inv.app (op K)).hom
    derivedDualHomologyLinearEquiv J n (DerivedCategory.Q.obj K) (e x) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app J := by
  let E := (derivedDualHomologyModelNatIso J n).app (op K)
  let p : (derivedDualHomologyFunctor J n).obj (DerivedCategory.Q.op.obj (op K)) →
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj J)⟦n⟧) :=
    derivedDualHomologyLinearEquiv J n (DerivedCategory.Q.obj K)
  let q : (moduleHomologyFunctor J n).obj (op K) →
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj J)⟦n⟧) :=
    fun x => moduleHomologyDerivedLinearEquiv K J n x ≫
      (DerivedCategory.Q.commShiftIso n).hom.app J
  have h : ∀ x, p x = q (E.hom.hom x) := derivedDualHomologyLinearEquiv_Q J n K
  exact (module_function_model_inverse E p q h (moduleCocycleClass K J n z)).trans
    (congrArg (fun f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (J⟦n⟧) =>
      f ≫ (DerivedCategory.Q.commShiftIso n).hom.app J)
      (moduleHomologyDerivedLinearEquiv_cocycle K J n z))

end CochainComplex.HomComplex
