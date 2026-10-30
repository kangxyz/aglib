/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Whiskering

/-!
# Transport of actual presheaf maps

Specified value equivalences transport a Type-valued presheaf. Supplied additive
maps with the literal transported value law lift through the faithful forgetful
functor, retaining those maps. Universe lifting uses the native additive functor.
-/

@[expose] public noncomputable section

universe u v

open Opposite

namespace CategoryTheory.PresheafTransport

/-- Transport the values of a Type-valued functor through specified equivalences. -/
def transportTypeFunctor {C : Type*} [Category* C] (P : C ⥤ Type u)
    (A : C → Type u) (e : ∀ T, P.obj T ≃ A T) : C ⥤ Type u where
  obj := A
  map {T U} f := ↾fun s => e U (P.map f ((e T).symm s))
  map_id T := by ext s; simp
  map_comp f g := by ext s; simp

/-- The specified value equivalences give the natural transport isomorphism. -/
def transportTypeFunctorIso {C : Type*} [Category* C] (P : C ⥤ Type u)
    (A : C → Type u) (e : ∀ T, P.obj T ≃ A T) :
    P ≅ transportTypeFunctor P A e :=
  NatIso.ofComponents (fun T => (e T).toIso) (by
    intro T U f
    ext h
    change e U (P.map f h) = e U (P.map f ((e T).symm (e T h)))
    rw [Equiv.symm_apply_apply])

/-- Lift an actual additive map with the native universe lift functor. -/
def liftSectionAddHom {A B : Type u} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    AddCommGrpCat.of (ULift.{v} A) ⟶ AddCommGrpCat.of (ULift.{v} B) :=
  AddCommGrpCat.uliftFunctor.{v, u}.map (AddCommGrpCat.ofHom f)

/-- The lifted map retains the supplied map's literal up/down value. -/
@[simp] theorem liftSectionAddHom_apply {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (s : ULift.{v} A) :
    liftSectionAddHom f s = ULift.up (f s.down) := rfl

/-- Lift an actual additive equivalence with the native universe lift functor. -/
def liftSectionAddIso {A B : Type u} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    AddCommGrpCat.of (ULift.{v} A) ≅ AddCommGrpCat.of (ULift.{v} B) :=
  AddCommGrpCat.uliftFunctor.{v, u}.mapIso
    (AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of A) (Y := AddCommGrpCat.of B) e)

/-- The lifted equivalence retains the supplied equivalence's literal up/down value. -/
@[simp] theorem liftSectionAddIso_hom_apply {A B : Type u} [AddCommGroup A]
    [AddCommGroup B] (e : A ≃+ B) (s : ULift.{v} A) :
    (liftSectionAddIso e).hom s = ULift.up (e s.down) := rfl

/-- Construct additive natural transformations from their literal component equations. -/
def sectionNatTrans {C : Type*} [Category* C] (P Q : C ⥤ AddCommGrpCat.{u})
    (a : ∀ T, P.obj T ⟶ Q.obj T)
    (h : ∀ {T U} (f : T ⟶ U) (s : P.obj T), a U (P.map f s) = Q.map f (a T s)) :
    P ⟶ Q where
  app := a
  naturality {T U} f := by ext s; exact h f s

/-- Construct additive natural isomorphisms from their literal component equations. -/
def sectionNatIso {C : Type*} [Category* C] (P Q : C ⥤ AddCommGrpCat.{u})
    (e : ∀ T, P.obj T ≅ Q.obj T)
    (h : ∀ {T U} (f : T ⟶ U) (s : P.obj T),
      (e U).hom (P.map f s) = Q.map f ((e T).hom s)) : P ≅ Q :=
  NatIso.ofComponents e (by intro T U f; ext s; exact h f s)

section Transport

variable {C : Type*} [Category* C]
    (P : Cᵒᵖ ⥤ Type u) (A : C → AddCommGrpCat.{u})
    (e : ∀ T, P.obj (op T) ≃ A T)
    (r : ∀ {T U}, (U ⟶ T) → (A T →+ A U))
    (hr : ∀ {T U} (f : U ⟶ T) (s : A T), r f s = e U (P.map f.op ((e T).symm s)))

/-- Lift the supplied additive restrictions through the faithful forgetful functor.
The Type presheaf proves the laws; no replacement restriction maps are chosen. -/
def liftAdditiveTransport : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Functor.Faithful.div
    (transportTypeFunctor P (fun T => A T.unop) (fun T => e T.unop) ⋙
      uliftFunctor.{u + 1})
    (forget AddCommGrpCat.{u + 1})
    (fun T => AddCommGrpCat.of (ULift.{u + 1} (A T.unop)))
    (fun _ => rfl)
    (fun f => liftSectionAddHom (r f.unop))
    (by
      intro T U f
      apply heq_of_eq
      apply ConcreteCategory.hom_ext
      intro s
      exact congrArg ULift.up (hr f.unop s.down))

/-- The supplied additive map is retained by the functor constructor. -/
theorem liftAdditiveTransport_map {T U : Cᵒᵖ} (f : T ⟶ U) :
    (liftAdditiveTransport P A e r hr).map f =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map (AddCommGrpCat.ofHom (r f.unop)) := rfl

/-- The defining restriction value is the literal universe lift of the supplied map. -/
@[simp] theorem liftAdditiveTransport_map_apply {T U : Cᵒᵖ} (f : T ⟶ U)
    (s : ULift.{u + 1} (A T.unop)) :
    (liftAdditiveTransport P A e r hr).map f s = ULift.up (r f.unop s.down) := rfl

/-- Forgetting the whole additive functor gives the lifted specified Type transport. -/
theorem liftAdditiveTransport_forget :
    liftAdditiveTransport P A e r hr ⋙ forget AddCommGrpCat.{u + 1} =
      transportTypeFunctor P (fun T => A T.unop) (fun T => e T.unop) ⋙
        uliftFunctor.{u + 1} := by
  refine Functor.hext ?_ ?_
  · intro T
    rfl
  · intro T U f
    apply heq_of_eq
    apply ConcreteCategory.hom_ext
    intro s
    exact congrArg ULift.up (hr f.unop s.down)

/-- Forgetting the additive transport retains the original lifted Type presheaf. -/
def liftAdditiveTransportForgetIso :
    liftAdditiveTransport P A e r hr ⋙ forget AddCommGrpCat.{u + 1} ≅
      P ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun T =>
    (Equiv.ulift.trans ((e T.unop).symm.trans Equiv.ulift.symm)).toIso) (by
      intro T U f
      apply ConcreteCategory.hom_ext
      intro s
      apply ULift.ext
      change (e U.unop).symm (r f.unop s.down) = P.map f ((e T.unop).symm s.down)
      rw [hr, Equiv.symm_apply_apply]
      rfl)

/-- The comparison's forward map uses exactly the specified inverse value equivalence. -/
theorem liftAdditiveTransportForgetIso_hom_app (T : Cᵒᵖ)
    (s : ULift.{u + 1} (A T.unop)) :
    (liftAdditiveTransportForgetIso P A e r hr).hom.app T s =
      ULift.up ((e T.unop).symm s.down) := rfl

/-- The comparison's inverse uses exactly the specified forward value equivalence. -/
theorem liftAdditiveTransportForgetIso_inv_app (T : Cᵒᵖ)
    (s : ULift.{u + 1} (P.obj T)) :
    (liftAdditiveTransportForgetIso P A e r hr).inv.app T s =
      ULift.up (e T.unop s.down) := rfl

/-- The whole comparison agrees with transport by the specified value equivalences. -/
theorem liftAdditiveTransportForgetIso_hom_comp :
    (liftAdditiveTransportForgetIso P A e r hr).hom ≫
        (Functor.isoWhiskerRight
          (transportTypeFunctorIso P (fun T => A T.unop) (fun T => e T.unop))
          uliftFunctor.{u + 1}).hom =
      eqToHom (liftAdditiveTransport_forget P A e r hr) := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.hom_ext
  intro s
  change ULift.up (e T.unop ((e T.unop).symm s.down)) =
    (eqToHom (liftAdditiveTransport_forget P A e r hr)).app T s
  rw [eqToHom_app]
  change ULift.up (e T.unop ((e T.unop).symm s.down)) = s
  exact ULift.ext _ _ ((e T.unop).apply_symm_apply s.down)

end Transport

/-- Additive transport preserves descent of the original Type presheaf.
The site and Hom bounds are those needed by the native forgetful sheaf criterion. -/
theorem liftAdditiveTransport_isSheaf {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type u)
    (A : C → AddCommGrpCat.{u}) (e : ∀ T, P.obj (op T) ≃ A T)
    (r : ∀ {T U}, (U ⟶ T) → (A T →+ A U))
    (hr : ∀ {T U} (f : U ⟶ T) (s : A T), r f s = e U (P.map f.op ((e T).symm s)))
    (hP : Presheaf.IsSheaf J P) : Presheaf.IsSheaf J (liftAdditiveTransport P A e r hr) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat.{u + 1})]
  apply (Presheaf.isSheaf_of_iso_iff (liftAdditiveTransportForgetIso P A e r hr)).2
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  exact Presieve.isSheaf_comp_uliftFunctor J ((isSheaf_iff_isSheaf_of_type _ _).1 hP)

section ComponentTransport

variable {C D : Type*} [Category* C] [Category* D]
    (P : Cᵒᵖ ⥤ Type u) (A : C → AddCommGrpCat.{u})
    (e : ∀ T, P.obj (op T) ≃ A T)
    (r : ∀ {T U}, (U ⟶ T) → (A T →+ A U))
    (hr : ∀ {T U} (f : U ⟶ T) (s : A T), r f s = e U (P.map f.op ((e T).symm s)))
    (Q : Dᵒᵖ ⥤ Type u) (B : D → AddCommGrpCat.{u})
    (e' : ∀ T, Q.obj (op T) ≃ B T)
    (r' : ∀ {T U}, (U ⟶ T) → (B T →+ B U))
    (hr' : ∀ {T U} (f : U ⟶ T) (s : B T), r' f s = e' U (Q.map f.op ((e' T).symm s)))
    (g : D ⥤ C)

/-- Natural additive maps between original Type transports, including base restriction. -/
def liftTransportHom (a : ∀ T, A (g.obj T) →+ B T)
    (ha : ∀ {T U} (f : U ⟶ T) (s : A (g.obj T)),
      a U (r (g.map f) s) = r' f (a T s)) :
    g.op ⋙ liftAdditiveTransport P A e r hr ⟶ liftAdditiveTransport Q B e' r' hr' where
  app T := liftSectionAddHom (a T.unop)
  naturality {T U} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    exact ha f.unop s.down

/-- Natural additive equivalences between original Type transports. -/
def liftTransportIso (a : ∀ T, A (g.obj T) ≃+ B T)
    (ha : ∀ {T U} (f : U ⟶ T) (s : A (g.obj T)),
      a U (r (g.map f) s) = r' f (a T s)) :
    g.op ⋙ liftAdditiveTransport P A e r hr ≅ liftAdditiveTransport Q B e' r' hr' :=
  NatIso.ofComponents (fun T => liftSectionAddIso (a T.unop)) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    exact ha f.unop s.down)

/-- Type naturality supplies the coherence for the specified additive equivalences. -/
def liftTransportIsoOfTypeIso
    (E : g.op ⋙ transportTypeFunctor P (fun T => A T.unop) (fun T => e T.unop) ≅
      transportTypeFunctor Q (fun T => B T.unop) (fun T => e' T.unop))
    (a : ∀ T, A (g.obj T) ≃+ B T)
    (ha : ∀ T (s : A (g.obj T)), a T s = E.hom.app (op T) s) :
    g.op ⋙ liftAdditiveTransport P A e r hr ≅ liftAdditiveTransport Q B e' r' hr' :=
  liftTransportIso P A e r hr Q B e' r' hr' g a (by
    intro T U f s
    rw [hr, hr', ha, ha]
    exact ConcreteCategory.congr_hom (E.hom.naturality f.op) s)

end ComponentTransport

/-- Compare an original Type transport with a native additive presheaf, before value lift. -/
def liftTransportNativeIso {C D : Type*} [Category* C] [Category* D]
    (P : Cᵒᵖ ⥤ Type u) (A : C → AddCommGrpCat.{u})
    (e : ∀ T, P.obj (op T) ≃ A T)
    (r : ∀ {T U}, (U ⟶ T) → (A T →+ A U))
    (hr : ∀ {T U} (f : U ⟶ T) (s : A T), r f s = e U (P.map f.op ((e T).symm s)))
    (g : D ⥤ C) (Q : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    (a : ∀ T, A (g.obj T) ≃+ Q.obj (op T))
    (ha : ∀ {T U} (f : U ⟶ T) (s : A (g.obj T)),
      a U (r (g.map f) s) = Q.map f.op (a T s)) :
    g.op ⋙ liftAdditiveTransport P A e r hr ≅ Q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents (fun T => liftSectionAddIso (a T.unop)) (by
    intro T U f
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    exact ha f.unop s.down)

/-- Same-site additive transport of the supplied component maps. -/
def liftTransportHomSame {C : Type*} [Category* C]
    (P : Cᵒᵖ ⥤ Type u) (A : C → AddCommGrpCat.{u})
    (e : ∀ T, P.obj (op T) ≃ A T)
    (r : ∀ {T U}, (U ⟶ T) → (A T →+ A U))
    (hr : ∀ {T U} (f : U ⟶ T) (s : A T), r f s = e U (P.map f.op ((e T).symm s)))
    (Q : Cᵒᵖ ⥤ Type u) (B : C → AddCommGrpCat.{u})
    (e' : ∀ T, Q.obj (op T) ≃ B T)
    (r' : ∀ {T U}, (U ⟶ T) → (B T →+ B U))
    (hr' : ∀ {T U} (f : U ⟶ T) (s : B T), r' f s = e' U (Q.map f.op ((e' T).symm s)))
    (a : ∀ T, A T →+ B T)
    (ha : ∀ {T U} (f : U ⟶ T) (s : A T), a U (r f s) = r' f (a T s)) :
    liftAdditiveTransport P A e r hr ⟶ liftAdditiveTransport Q B e' r' hr' where
  app T := liftSectionAddHom (a T.unop)
  naturality {T U} f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    exact ha f.unop s.down

end CategoryTheory.PresheafTransport
