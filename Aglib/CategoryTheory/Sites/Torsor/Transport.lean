/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsor.Hom
public import Aglib.CategoryTheory.TorsorAction.Basic
public import Mathlib.CategoryTheory.Endomorphism

/-! # Positive transport and characters on the original torsors

Positive transport from `s` to `t` is the existing augmentation difference
`t` minus `s`. Existing sections suffice; no nonemptiness instance is added.
The character uses the original contravariant restriction maps and the
explicit hypothesis that those maps fix the coefficient sections.

Categorical transport uses the existing `TorsorAction` and its unique
generalized-point transport. Carrier and coefficient isomorphisms reindex
that same action through their actual morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Opposite

namespace CategoryTheory.Sheaf.Torsor

universe u v w h
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {L M : Sheaf J AddCommGrpCat.{w}}

/-- The existing positive difference, acting on the first section to give the second. -/
def positiveTransport (P : Torsor L) (U : Cᵒᵖ) (s t : P.carrier.obj.obj U) : L.obj.obj U :=
  letI := P.sectionAction U
  AddAction.TorsorAugmentation.difference (P.unique_transport U) t s

/-- The historical section-equivalence inverse is this same positive transport by uniqueness. -/
theorem positiveTransport_eq_sectionEquiv_symm (P : Torsor L) (U : Cᵒᵖ)
    (s t : P.carrier.obj.obj U) :
    P.positiveTransport U s t = (P.sectionEquiv U s).symm t :=
  (P.sectionEquiv_symm_eq_difference U s t).symm

@[simp] theorem action_positiveTransport (P : Torsor L) (U : Cᵒᵖ)
    (s t : P.carrier.obj.obj U) : P.action U (P.positiveTransport U s t) s = t := by
  let := P.sectionAction U
  exact AddAction.TorsorAugmentation.difference_vadd (P.unique_transport U) t s

/-- Every actual translating coefficient is the same selected positive difference. -/
theorem positiveTransport_eq (P : Torsor L) (U : Cᵒᵖ) (s t : P.carrier.obj.obj U)
    (a : L.obj.obj U) (ha : P.action U a s = t) : P.positiveTransport U s t = a := by
  let := P.sectionAction U
  exact AddAction.TorsorAugmentation.difference_eq (P.unique_transport U) t s a ha

@[simp] theorem positiveTransport_self (P : Torsor L) (U : Cᵒᵖ)
    (s : P.carrier.obj.obj U) : P.positiveTransport U s s = 0 := by
  let := P.sectionAction U
  exact AddAction.TorsorAugmentation.difference_self (P.unique_transport U) s

/-- The positive displacements add in the order of the original section chain. -/
theorem positiveTransport_trans (P : Torsor L) (U : Cᵒᵖ)
    (s t r : P.carrier.obj.obj U) :
    P.positiveTransport U s t + P.positiveTransport U t r = P.positiveTransport U s r := by
  let := P.sectionAction U
  exact (add_comm _ _).trans
    (AddAction.TorsorAugmentation.difference_chain (P.unique_transport U) r t s).symm

/-- Restriction preserves the actual positive difference. -/
theorem positiveTransport_naturality (P : Torsor L) {U V : Cᵒᵖ} (f : U ⟶ V)
    (s t : P.carrier.obj.obj U) :
    L.obj.map f (P.positiveTransport U s t) =
      P.positiveTransport V (P.carrier.obj.map f s) (P.carrier.obj.map f t) := by
  let := P.sectionAction U
  let := P.sectionAction V
  exact (AddAction.TorsorAugmentation.difference_naturality (P.unique_transport U)
    (P.unique_transport V) (L.obj.map f).hom (P.carrier.obj.map f)
      (P.naturality f) t s).symm

/-- An actual coefficient-relative torsor map preserves positive transport. -/
theorem positiveTransport_hom {P : Torsor L} {Q : Torsor M} {q : L ⟶ M}
    (e : Torsor.Hom q P Q) (U : Cᵒᵖ) (s t : P.carrier.obj.obj U) :
    Q.positiveTransport U (e.map.hom.app U s) (e.map.hom.app U t) =
      q.hom.app U (P.positiveTransport U s t) := by
  let := P.sectionAction U
  let := Q.sectionAction U
  exact AddAction.TorsorAugmentation.difference_naturality (P.unique_transport U)
    (Q.unique_transport U) (q.hom.app U).hom (e.map.hom.app U) (e.equivariant U) t s

/-- Same-coefficient equivariant carrier isomorphisms preserve the literal difference. -/
theorem positiveTransport_iso {P Q : Torsor L} (e : Torsor.Iso P Q)
    (U : Cᵒᵖ) (s t : P.carrier.obj.obj U) :
    Q.positiveTransport U (e.carrierIso.hom.hom.app U s)
      (e.carrierIso.hom.hom.app U t) = P.positiveTransport U s t := by
  apply Q.positiveTransport_eq
  rw [← e.equivariant, P.action_positiveTransport]

section Character
variable {H : Type h} [Group H] (P : Torsor L) (U : C) (ρ : H →* Aut U)

/-- Positive transport from a frame to its original contravariant restriction. -/
def framedScalar (s : P.carrier.obj.obj (op U)) (g : H) : L.obj.obj (op U) :=
  P.positiveTransport (op U) s (P.carrier.obj.map (ρ g).hom.op s)

@[simp] theorem framedScalar_one (s : P.carrier.obj.obj (op U)) :
    P.framedScalar U ρ s 1 = 0 := by
  simp only [framedScalar, map_one]
  change P.positiveTransport (op U) s (P.carrier.obj.map (𝟙 (op U)) s) = 0
  rw [Functor.map_id]
  exact P.positiveTransport_self (op U) s

variable (hunit : ∀ g : H, ∀ a : L.obj.obj (op U), L.obj.map (ρ g).hom.op a = a)

include hunit in
/-- Actual contravariant Aut composition makes the scalar additive when coefficients are fixed. -/
theorem framedScalar_mul (s : P.carrier.obj.obj (op U)) (g k : H) :
    P.framedScalar U ρ s (g * k) = P.framedScalar U ρ s g + P.framedScalar U ρ s k := by
  have hm : P.carrier.obj.map (ρ (g * k)).hom.op s =
      P.carrier.obj.map (ρ k).hom.op (P.carrier.obj.map (ρ g).hom.op s) := by
    rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom, op_comp, Functor.map_comp]
    rfl
  dsimp only [framedScalar]
  rw [hm, ← P.positiveTransport_trans (op U) s (P.carrier.obj.map (ρ k).hom.op s),
    ← P.positiveTransport_naturality (ρ k).hom.op]
  rw [hunit, add_comm]

/-- The character of a supplied frame, with the original coefficient-fixedness premise. -/
def framedCharacter (s : P.carrier.obj.obj (op U)) : H →* Multiplicative (L.obj.obj (op U)) where
  toFun g := Multiplicative.ofAdd (P.framedScalar U ρ s g)
  map_one' := P.framedScalar_one U ρ s
  map_mul' := P.framedScalar_mul U ρ hunit s

include hunit in
/-- The actual evaluation scalar is independent of the supplied frame. -/
theorem framedScalar_independent (s t : P.carrier.obj.obj (op U)) (g : H) :
    P.framedScalar U ρ s g = P.framedScalar U ρ t g := by
  let rs := P.carrier.obj.map (ρ g).hom.op s
  let rt := P.carrier.obj.map (ρ g).hom.op t
  have hn : P.positiveTransport (op U) rs rt = P.positiveTransport (op U) s t :=
    (P.positiveTransport_naturality (ρ g).hom.op s t).symm.trans (hunit g _)
  have h₁ := P.positiveTransport_trans (op U) s t rt
  have h₂ := P.positiveTransport_trans (op U) s rs rt
  rw [hn] at h₂
  have he : P.framedScalar U ρ s g + P.positiveTransport (op U) s t =
      P.framedScalar U ρ t g + P.positiveTransport (op U) s t :=
    h₂.trans (h₁.symm.trans (add_comm _ _))
  exact add_right_cancel he

theorem framedCharacter_independent (s t : P.carrier.obj.obj (op U)) :
    P.framedCharacter U ρ hunit s = P.framedCharacter U ρ hunit t := by
  apply MonoidHom.ext
  intro g
  exact congrArg Multiplicative.ofAdd (P.framedScalar_independent U ρ hunit s t g)

/-- An equivariant carrier isomorphism preserves the scalar on the same original test object. -/
theorem framedScalar_iso {Q : Torsor L} (e : Torsor.Iso P Q)
    (s : P.carrier.obj.obj (op U)) (g : H) :
    P.framedScalar U ρ s g =
      Q.framedScalar U ρ (e.carrierIso.hom.hom.app (op U) s) g := by
  have hn : e.carrierIso.hom.hom.app (op U) (P.carrier.obj.map (ρ g).hom.op s) =
      Q.carrier.obj.map (ρ g).hom.op (e.carrierIso.hom.hom.app (op U) s) :=
    congrArg (fun a => a s) (e.carrierIso.hom.hom.naturality (ρ g).hom.op)
  dsimp only [framedScalar]
  rw [← hn, positiveTransport_iso]

include hunit in
/-- The frame-independent evaluation agrees on the original equivariantly isomorphic torsors. -/
theorem framedScalar_iso_independent {Q : Torsor L} (e : Torsor.Iso P Q)
    (s : P.carrier.obj.obj (op U)) (t : Q.carrier.obj.obj (op U)) (g : H) :
    P.framedScalar U ρ s g = Q.framedScalar U ρ t g :=
  (P.framedScalar_iso U ρ e s g).trans (Q.framedScalar_independent U ρ hunit _ t g)

theorem framedCharacter_iso_independent {Q : Torsor L} (e : Torsor.Iso P Q)
    (s : P.carrier.obj.obj (op U)) (t : Q.carrier.obj.obj (op U)) :
    P.framedCharacter U ρ hunit s = Q.framedCharacter U ρ hunit t := by
  apply MonoidHom.ext
  intro g
  exact congrArg Multiplicative.ofAdd (P.framedScalar_iso_independent U ρ hunit e s t g)

end Character
end CategoryTheory.Sheaf.Torsor

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace CategoryTheory

universe u v u' v'
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B : Grp C} {X : C}

/-- The original unique positive transporter between two existing generalized points. -/
def TorsorAction.positiveTransport (τ : TorsorAction A (toUnit X)) {T : C}
    (x y : T ⟶ X) : T ⟶ A.X :=
  Classical.choose (τ.transport x y (toUnit_unique _ _))

@[simp] theorem TorsorAction.act_positiveTransport (τ : TorsorAction A (toUnit X))
    {T : C} (x y : T ⟶ X) : τ.act (τ.positiveTransport x y) x = y :=
  (Classical.choose_spec (τ.transport x y (toUnit_unique _ _))).1

/-- Equality with any chosen transporter is proved by its original action equation. -/
theorem TorsorAction.positiveTransport_eq (τ : TorsorAction A (toUnit X))
    {T : C} (x y : T ⟶ X) (a : T ⟶ A.X) (ha : τ.act a x = y) :
    τ.positiveTransport x y = a :=
  ((Classical.choose_spec (τ.transport x y (toUnit_unique _ _))).2 a ha).symm

@[simp] theorem TorsorAction.positiveTransport_act (τ : TorsorAction A (toUnit X))
    {T : C} (a : T ⟶ A.X) (x : T ⟶ X) : τ.positiveTransport x (τ.act a x) = a :=
  τ.positiveTransport_eq x (τ.act a x) a rfl

/-- The original categorical positive transporter is natural in the test object. -/
theorem TorsorAction.positiveTransport_naturality (τ : TorsorAction A (toUnit X))
    {T U : C} (g : T ⟶ U) (x y : U ⟶ X) :
    g ≫ τ.positiveTransport x y = τ.positiveTransport (g ≫ x) (g ≫ y) := by
  symm
  apply τ.positiveTransport_eq
  rw [← τ.naturality, τ.act_positiveTransport]

/-- The actual product morphism representing positive transport. -/
def TorsorAction.positiveDifferenceMap (τ : TorsorAction A (toUnit X)) : X ⊗ X ⟶ A.X :=
  τ.positiveTransport (fst X X) (snd X X)

theorem TorsorAction.comp_positiveDifferenceMap (τ : TorsorAction A (toUnit X))
    {T : C} (x y : T ⟶ X) :
    lift x y ≫ τ.positiveDifferenceMap = τ.positiveTransport x y := by
  rw [TorsorAction.positiveDifferenceMap, τ.positiveTransport_naturality, lift_fst, lift_snd]

section MapNaturality
variable {D : Type u'} [Category.{v'} D] [CartesianMonoidalCategory D]
  {B' : Grp D} {Y : D}

/-- Actual equivariant point and coefficient maps preserve the unique positive transporter.
The source and target categories and test objects remain independently sized. -/
theorem TorsorAction.positiveTransport_map (τ : TorsorAction A (toUnit X))
    (σ : TorsorAction B' (toUnit Y)) {T : C} {U : D}
    (q : (T ⟶ A.X) → (U ⟶ B'.X)) (r : (T ⟶ X) → (U ⟶ Y))
    (heq : ∀ a x, r (τ.act a x) = σ.act (q a) (r x)) (x y : T ⟶ X) :
    q (τ.positiveTransport x y) = σ.positiveTransport (r x) (r y) := by
  symm
  apply σ.positiveTransport_eq
  rw [← heq, τ.act_positiveTransport]

end MapNaturality

/-- Reindex the original action by an actual carrier isomorphism. -/
def TorsorAction.transportCarrier (τ : TorsorAction A (toUnit X)) {Z : C} (e : Z ≅ X) :
    TorsorAction A (toUnit Z) where
  act a x := τ.act a (x ≫ e.hom) ≫ e.inv
  naturality g a x := by rw [← Category.assoc, τ.naturality, Category.assoc]
  one_act x := by simp only [τ.one_act, Category.assoc, e.hom_inv_id, Category.comp_id]
  mul_act a b x := by simp only [τ.mul_act, Category.assoc, e.inv_hom_id, Category.comp_id]
  over _ _ := toUnit_unique _ _
  transport x y _ := by
    obtain ⟨a, ha, hu⟩ := τ.transport (x ≫ e.hom) (y ≫ e.hom) (toUnit_unique _ _)
    refine ⟨a, ?_, ?_⟩
    · simp only [ha, Category.assoc, e.hom_inv_id, Category.comp_id]
    · intro b hb
      apply hu
      have h := congrArg (fun k => k ≫ e.hom) hb
      simpa only [Category.assoc, e.inv_hom_id, Category.comp_id] using h

/-- Carrier reindexing retains the same actual translating coefficient. -/
theorem TorsorAction.transportCarrier_positiveTransport (τ : TorsorAction A (toUnit X))
    {Z T : C} (e : Z ≅ X) (x y : T ⟶ Z) :
    (τ.transportCarrier e).positiveTransport x y =
      τ.positiveTransport (x ≫ e.hom) (y ≫ e.hom) := by
  apply (τ.transportCarrier e).positiveTransport_eq
  simp only [TorsorAction.transportCarrier, τ.act_positiveTransport,
    Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Coefficient reindexing uses the inverse of the actual group-object isomorphism. -/
def TorsorAction.ofCoefficientIso (τ : TorsorAction A (toUnit X)) (e : A ≅ B) :
    TorsorAction B (toUnit X) where
  act a x := τ.act (a ≫ e.inv.hom.hom) x
  naturality g a x := by rw [τ.naturality, Category.assoc]
  one_act x := by simp only [MonObj.one_comp, τ.one_act]
  mul_act a b x := by simp only [MonObj.mul_comp, τ.mul_act]
  over _ _ := toUnit_unique _ _
  transport {T} x y _ := by
    obtain ⟨a, ha, hu⟩ := τ.transport x y (toUnit_unique _ _)
    have hleft : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 A.X :=
      congrArg (fun q : A ⟶ A => q.hom.hom) e.hom_inv_id
    have hright : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 B.X :=
      congrArg (fun q : B ⟶ B => q.hom.hom) e.inv_hom_id
    refine ⟨a ≫ e.hom.hom.hom, ?_, ?_⟩
    · simpa only [Category.assoc, hleft, Category.comp_id] using ha
    · intro b hb
      have h := congrArg (fun c : T ⟶ A.X => c ≫ e.hom.hom.hom) (hu _ hb)
      simpa only [Category.assoc, hright, Category.comp_id] using h

/-- The forward original coefficient morphism recovers the original action value. -/
theorem TorsorAction.ofCoefficientIso_hom_act
    (τ : TorsorAction A (toUnit X)) (e : A ≅ B) {T : C} (a : T ⟶ A.X) (x : T ⟶ X) :
    (τ.ofCoefficientIso e).act (a ≫ e.hom.hom.hom) x = τ.act a x := by
  have hleft : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 A.X :=
    congrArg (fun q : A ⟶ A => q.hom.hom) e.hom_inv_id
  change τ.act ((a ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) x = τ.act a x
  rw [Category.assoc, hleft, Category.comp_id]

/-- The same carrier's positive transporter changes by the forward coefficient morphism. -/
theorem TorsorAction.ofCoefficientIso_positiveTransport
    (τ : TorsorAction A (toUnit X)) (e : A ≅ B) {T : C} (x y : T ⟶ X) :
    (τ.ofCoefficientIso e).positiveTransport x y =
      τ.positiveTransport x y ≫ e.hom.hom.hom := by
  apply (τ.ofCoefficientIso e).positiveTransport_eq
  rw [τ.ofCoefficientIso_hom_act, τ.act_positiveTransport]

end CategoryTheory
