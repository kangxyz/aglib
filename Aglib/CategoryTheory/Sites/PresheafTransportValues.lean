/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.PresheafTransport

/-! # Original values of the complete additive transport isomorphism -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.PresheafTransport

universe u

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

/-- The original transported component evaluates through the supplied additive
isomorphism, retaining the genuine value-universe lift. -/
theorem liftTransportIsoOfTypeIso_hom_down
    (E : g.op ⋙ transportTypeFunctor P (fun T => A T.unop) (fun T => e T.unop) ≅
      transportTypeFunctor Q (fun T => B T.unop) (fun T => e' T.unop))
    (a : ∀ T, A (g.obj T) ≃+ B T)
    (ha : ∀ T (s : A (g.obj T)), a T s = E.hom.app (op T) s)
    (T : D) (s : ULift.{u + 1} (A (g.obj T))) :
    (((liftTransportIsoOfTypeIso P A e r hr Q B e' r' hr' g E a ha).hom.app
      (op T)) s).down = a T s.down := rfl

end CategoryTheory.PresheafTransport
