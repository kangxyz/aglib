/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AdditiveSections

/-! # Typed additive component transport -/

@[expose] public noncomputable section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Lift an actual additive map before specializing its carriers. -/
def liftSectionAddHom {A B : Type u} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    AddCommGrpCat.of (ULift.{v} A) ⟶ AddCommGrpCat.of (ULift.{v} B) :=
  AddCommGrpCat.ofHom {
    toFun s := ⟨f s.down⟩
    map_zero' := ULift.ext _ _ (map_zero f)
    map_add' s t := ULift.ext _ _ (map_add f s.down t.down) }

/-- Lift an actual additive equivalence before specializing its carriers. -/
def liftSectionAddIso {A B : Type u} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    AddCommGrpCat.of (ULift.{v} A) ≅ AddCommGrpCat.of (ULift.{v} B) :=
  AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (e.trans AddEquiv.ulift.symm))

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

/-- Natural additive maps between two original Type transports, including base restriction. -/
def liftTransportHom (a : ∀ T, A (g.obj T) →+ B T)
    (ha : ∀ {T U} (f : U ⟶ T) (s : A (g.obj T)),
      a U (r (g.map f) s) = r' f (a T s)) :
    g.op ⋙ liftAdditiveTransport P A e r hr ⟶ liftAdditiveTransport Q B e' r' hr' where
  app T := liftSectionAddHom (a T.unop)
  naturality {T U} f := by
    ext s
    apply ULift.ext
    exact ha f.unop s.down

/-- Natural additive equivalences between two original Type transports. -/
def liftTransportIso (a : ∀ T, A (g.obj T) ≃+ B T)
    (ha : ∀ {T U} (f : U ⟶ T) (s : A (g.obj T)),
      a U (r (g.map f) s) = r' f (a T s)) :
    g.op ⋙ liftAdditiveTransport P A e r hr ≅ liftAdditiveTransport Q B e' r' hr' :=
  NatIso.ofComponents (fun T => liftSectionAddIso (a T.unop)) (by
    intro T U f
    ext s
    apply ULift.ext
    exact ha f.unop s.down)

/-- Native Type naturality supplies the coherence for additive equivalences,
without unfolding concrete transported carriers in the naturality proof. -/
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

end Transport

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
    g.op ⋙ liftAdditiveTransport P A e r hr ≅ Q ⋙ AddCommGrpCat.uliftFunctor.{u+1,u} :=
  NatIso.ofComponents (fun T => liftSectionAddIso (a T.unop)) (by
    intro T U f
    ext s
    apply ULift.ext
    exact ha f.unop s.down)

/-- Same-site additive transport, with identity functor coherence absorbed abstractly. -/
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
    ext s
    apply ULift.ext
    exact ha f.unop s.down

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
