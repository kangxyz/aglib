/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-!
# Natural-transformation component equations for native mates

These typed equations normalize the small `TwoSquare` constructor before specialization
at derived functors. The exchange map remains Mathlib's `mateEquiv`.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F}
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : G ⋙ L₂ ⟶ L₁ ⋙ H)

/-- Component formula with the natural-transformation square exposed in the statement. -/
theorem mateEquiv_mk_natTrans_app (K : D) :
    (mateEquiv adj₁ adj₂ (TwoSquare.mk G L₁ L₂ H α)).natTrans.app K =
      adj₂.unit.app (G.obj (R₁.obj K)) ≫ R₂.map (α.app (R₁.obj K)) ≫
        R₂.map (H.map (adj₁.counit.app K)) :=
  mateEquiv_app_eq adj₁ adj₂ (TwoSquare.mk G L₁ L₂ H α) K

/-- The adjoint equation, normalized before substituting any derived functors. -/
theorem mateEquiv_mk_natTrans_counit (K : D) :
    L₂.map ((mateEquiv adj₁ adj₂ (TwoSquare.mk G L₁ L₂ H α)).natTrans.app K) ≫
        adj₂.counit.app (H.obj K) =
      α.app (R₁.obj K) ≫ H.map (adj₁.counit.app K) :=
  mateEquiv_counit adj₁ adj₂ (TwoSquare.mk G L₁ L₂ H α) K


/-- The native mate component equality, kept as a shared proposition for specialization. -/
def MateComponentEquation (K : D) : Prop :=
  (mateEquiv adj₁ adj₂ (TwoSquare.mk G L₁ L₂ H α)).natTrans.app K =
    adj₂.unit.app (G.obj (R₁.obj K)) ≫ R₂.map (α.app (R₁.obj K)) ≫
      R₂.map (H.map (adj₁.counit.app K))

/-- The component equation of the actual native mate. -/
theorem mateComponentEquation (K : D) : MateComponentEquation adj₁ adj₂ α K :=
  mateEquiv_mk_natTrans_app adj₁ adj₂ α K

/-- The native counit equality, kept as a shared proposition for specialization. -/
def MateCounitEquation (K : D) : Prop :=
  L₂.map ((mateEquiv adj₁ adj₂ (TwoSquare.mk G L₁ L₂ H α)).natTrans.app K) ≫
      adj₂.counit.app (H.obj K) =
    α.app (R₁.obj K) ≫ H.map (adj₁.counit.app K)

/-- The adjoint equation of the actual native mate. -/
theorem mateCounitEquation (K : D) : MateCounitEquation adj₁ adj₂ α K :=
  mateEquiv_mk_natTrans_counit adj₁ adj₂ α K


section Transport

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {S : A ⥤ B} {L M : B ⥤ C} {H : C ⥤ D} {U V : A ⥤ D}

/-- A whiskered transformation transported at both ends, with all five component maps. -/
theorem whiskeredTransport_app (α : U ⟶ S ⋙ L ⋙ H) (β : L ⟶ M)
    (γ : S ⋙ M ⋙ H ⟶ V) (X : A) {P Q : D}
    (a : U.obj X ⟶ P) (b : P ⟶ H.obj (L.obj (S.obj X)))
    (c : H.obj (M.obj (S.obj X)) ⟶ Q) (d : Q ⟶ V.obj X)
    (hα : α.app X = a ≫ b) (hγ : γ.app X = c ≫ d) :
    (α ≫ Functor.whiskerLeft S (Functor.whiskerRight β H) ≫ γ).app X =
      a ≫ b ≫ H.map (β.app (S.obj X)) ≫ c ≫ d := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    hα, hγ, Category.assoc]

/-- The five-map transported component formula as a shared proposition. -/
def WhiskeredTransportEquation (α : U ⟶ S ⋙ L ⋙ H) (β : L ⟶ M)
    (γ : S ⋙ M ⋙ H ⟶ V) (X : A) {P Q : D}
    (a : U.obj X ⟶ P) (b : P ⟶ H.obj (L.obj (S.obj X)))
    (c : H.obj (M.obj (S.obj X)) ⟶ Q) (d : Q ⟶ V.obj X) : Prop :=
  (α ≫ Functor.whiskerLeft S (Functor.whiskerRight β H) ≫ γ).app X =
    a ≫ b ≫ H.map (β.app (S.obj X)) ≫ c ≫ d

/-- The shared transported formula follows from the two endpoint component equations. -/
theorem whiskeredTransportEquation (α : U ⟶ S ⋙ L ⋙ H) (β : L ⟶ M)
    (γ : S ⋙ M ⋙ H ⟶ V) (X : A) {P Q : D}
    (a : U.obj X ⟶ P) (b : P ⟶ H.obj (L.obj (S.obj X)))
    (c : H.obj (M.obj (S.obj X)) ⟶ Q) (d : Q ⟶ V.obj X)
    (hα : α.app X = a ≫ b) (hγ : γ.app X = c ≫ d) :
    WhiskeredTransportEquation α β γ X a b c d :=
  whiskeredTransport_app α β γ X a b c d hα hγ

end Transport

end CategoryTheory
