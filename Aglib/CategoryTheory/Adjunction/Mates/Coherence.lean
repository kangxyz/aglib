/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-!
# Whole comparison coherence for native exchange squares

The existing comparison chase retains its original arrows, isomorphisms and
equality transports. Its equations are proved separately from its data, and a
whole natural-transformation equation is evaluated only after it is proved.
This module uses the native mate and comparison formulas from Mates.Whole;
it has no derived-category, site, coefficient or geometric-model data.
-/

@[expose] public section

section OriginalCoherenceChain

namespace CategoryTheory

variable {C : Type*} [Category* C]
  {A B C₀ D E F G H I J K L M N O : C}
  {p : A ⟶ B} {q : B ⟶ C₀} {b₀ : C₀ ⟶ D} {t₂ : D ⟶ E}
  {c₀ : E ⟶ F} {d : G ≅ F} {t₁ : G ⟶ H} {e₀ : H ⟶ I}
  {a : A ⟶ J} {m : J ⟶ D} {b : J ⟶ K} {n : K ⟶ E}
  {c : K ⟶ L} {r : L ⟶ G} {e : L ⟶ M} {s : M ⟶ H}
  {z : M ⟶ N} {u : N ⟶ O} {v : O ⟶ I} {τ : A ⟶ N}

/-- The exchange chase is formal once its actual five comparison equations are supplied. -/
theorem exchangeCoherence_chain
    (h₁ : p ≫ q ≫ b₀ = a ≫ m)
    (h₂ : m ≫ t₂ = b ≫ n)
    (h₃ : n ≫ c₀ = c ≫ r ≫ d.hom)
    (h₄ : r ≫ t₁ = e ≫ s)
    (h₅ : s ≫ e₀ = z ≫ u ≫ v)
    (ht : a ≫ b ≫ c ≫ e ≫ z = τ) :
    p ≫ q ≫ b₀ ≫ t₂ ≫ c₀ ≫ d.inv ≫ t₁ ≫ e₀ = τ ≫ u ≫ v := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% h₄, h₅]
  rw [reassoc_of% ht]

end CategoryTheory

end OriginalCoherenceChain

section OriginalRawArrowNormalization

namespace CategoryTheory

/-- Normalize actual component arrows using only raw square and inverse equations. -/
theorem exchangeCoherence_normalize_arrows
    {C D : Type*} [Category* C] [Category* D] (F : D ⥤ C)
    {X Y Z U V W Q : C} {A B C₀ D₀ : D}
    (p : Z ⟶ X) (pi : X ⟶ Z) (b : U ⟶ Y) (bi : Y ⟶ U)
    (t : U ⟶ V) (c : V ⟶ F.obj A)
    (d : B ⟶ A) (di : A ⟶ B) (r : B ⟶ C₀) (e : C₀ ⟶ D₀)
    (τ : Z ⟶ W) (u : W ⟶ Q) (q : X ⟶ Y) (v : Q ⟶ F.obj D₀)
    (s₁ : A ⟶ D₀) (s₂ : Y ⟶ F.obj A) (s : X ⟶ Q)
    (hp : pi ≫ p = 𝟙 X) (hb : bi ≫ b = 𝟙 Y) (hd : di ≫ d = 𝟙 A)
    (h₁ : d ≫ s₁ = r ≫ e) (h₂ : b ≫ s₂ = t ≫ c) (h : p ≫ s = τ ≫ u)
    (hc : p ≫ q ≫ bi ≫ t ≫ c ≫ F.map di ≫ F.map r ≫ F.map e =
      τ ≫ u ≫ v) :
    q ≫ s₂ ≫ F.map s₁ = s ≫ v := by
  rw [← F.map_comp r e, ← h₁, F.map_comp d s₁] at hc
  rw [← CategoryTheory.Functor.map_comp_assoc, hd,
    CategoryTheory.Functor.map_id, Category.id_comp] at hc
  rw [← reassoc_of% h₂, reassoc_of% hb, ← reassoc_of% h] at hc
  have hc' := congrArg (fun k => pi ≫ k) hc
  simpa only [← Category.assoc, hp, Category.id_comp] using hc'

/-- Rotate a comparison equation using only its primitive inverse witnesses. -/
theorem exchangeCoherence_rotate_start
    {C : Type*} [Category* C] {A B D E F : C}
    (a : A ⟶ B) (ai : B ⟶ A) (p : B ⟶ D) (q : D ⟶ E)
    (m : A ⟶ F) (b : F ⟶ E) (bi : E ⟶ F)
    (ha : ai ≫ a = 𝟙 B) (hb : b ≫ bi = 𝟙 F)
    (h : a ≫ p ≫ q = m ≫ b) :
    p ≫ q ≫ bi = ai ≫ m := by
  have hc := congrArg (fun z => ai ≫ z ≫ bi) h
  simpa only [Category.assoc, reassoc_of% ha, hb, Category.id_comp,
    Category.comp_id] using hc

/-- Rotate the terminal comparison using a primitive inverse witness. -/
theorem exchangeCoherence_rotate_finish
    {C : Type*} [Category* C] {A B D : C}
    (a : A ⟶ B) (ai : B ⟶ A) (p : B ⟶ D) (q : A ⟶ D)
    (ha : ai ≫ a = 𝟙 B) (h : a ≫ p = q) :
    p = ai ≫ q := by
  have hc := congrArg (fun z => ai ≫ z) h
  simpa only [← Category.assoc, ha, Category.id_comp] using hc

/-- Functors preserve a specified inverse equation without constructing a mapped iso. -/
theorem exchangeCoherence_map_inverse
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y : C} (d : X ⟶ Y) (di : Y ⟶ X) (hd : d ≫ di = 𝟙 X) :
    F.map d ≫ F.map di = 𝟙 (F.obj X) := by
  rw [← F.map_comp, hd, F.map_id]

/-- The comparison chase with primitive arrows and a specified inverse equation. -/
theorem exchangeCoherence_chain_arrows
    {C : Type*} [Category* C]
    {A B C₀ D E F G H I J K L M N O : C}
    {p : A ⟶ B} {q : B ⟶ C₀} {b₀ : C₀ ⟶ D} {t₂ : D ⟶ E}
    {c₀ : E ⟶ F} (d : G ⟶ F) (di : F ⟶ G)
    {t₁ : G ⟶ H} {e₀ : H ⟶ I}
    {a : A ⟶ J} {m : J ⟶ D} {b : J ⟶ K} {n : K ⟶ E}
    {c : K ⟶ L} {r : L ⟶ G} {e : L ⟶ M} {s : M ⟶ H}
    {z : M ⟶ N} {u : N ⟶ O} {v : O ⟶ I} {τ : A ⟶ N}
    (hd : d ≫ di = 𝟙 G)
    (h₁ : p ≫ q ≫ b₀ = a ≫ m)
    (h₂ : m ≫ t₂ = b ≫ n)
    (h₃ : n ≫ c₀ = c ≫ r ≫ d)
    (h₄ : r ≫ t₁ = e ≫ s)
    (h₅ : s ≫ e₀ = z ≫ u ≫ v)
    (ht : a ≫ b ≫ c ≫ e ≫ z = τ) :
    p ≫ q ≫ b₀ ≫ t₂ ≫ c₀ ≫ di ≫ t₁ ≫ e₀ = τ ≫ u ≫ v := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  simp only [reassoc_of% hd]
  rw [reassoc_of% h₄, h₅]
  rw [reassoc_of% ht]

/-- A functor-valued comparison chase closes equality transport before specialization.
The six source indices carry only actual equalities; the closing pentagon is proved,
not supplied as an additional coherence hypothesis. -/
theorem exchangeCoherence_chain_natTransport
    {I C D : Type*} [Category* C] [Category* D]
    (P : I → C ⥤ D) (A : C) {x₀ x₁ x₂ x₃ x₄ x₅ : I}
    (e₁₀ : x₁ = x₀) (e₁₂ : x₁ = x₂) (e₂₃ : x₂ = x₃)
    (e₃₄ : x₃ = x₄) (e₅₄ : x₅ = x₄) (e₀₅ : x₀ = x₅)
    {B₀ C₀ D₀ E₀ F₀ G₀ H₀ I₀ O₀ : D}
    {p : (P x₀).obj A ⟶ B₀} {q : B₀ ⟶ C₀} {b₀ : C₀ ⟶ D₀}
    {t₂ : D₀ ⟶ E₀} {c₀ : E₀ ⟶ F₀} (d : G₀ ⟶ F₀) (di : F₀ ⟶ G₀)
    {t₁ : G₀ ⟶ H₀} {e₀ : H₀ ⟶ I₀}
    {m : (P x₁).obj A ⟶ D₀} {n : (P x₂).obj A ⟶ E₀}
    {r : (P x₃).obj A ⟶ G₀} {s : (P x₄).obj A ⟶ H₀}
    {u : (P x₅).obj A ⟶ O₀} {v : O₀ ⟶ I₀}
    (hd : d ≫ di = 𝟙 G₀)
    (h₁ : p ≫ q ≫ b₀ = (eqToIso (congrArg P e₁₀)).inv.app A ≫ m)
    (h₂ : m ≫ t₂ = (eqToIso (congrArg P e₁₂)).hom.app A ≫ n)
    (h₃ : n ≫ c₀ = (eqToIso (congrArg P e₂₃)).hom.app A ≫ r ≫ d)
    (h₄ : r ≫ t₁ = (eqToIso (congrArg P e₃₄)).hom.app A ≫ s)
    (h₅ : s ≫ e₀ = (eqToIso (congrArg P e₅₄)).inv.app A ≫ u ≫ v) :
    p ≫ q ≫ b₀ ≫ t₂ ≫ c₀ ≫ di ≫ t₁ ≫ e₀ =
      (eqToIso (congrArg P e₀₅)).hom.app A ≫ u ≫ v := by
  refine exchangeCoherence_chain_arrows d di hd h₁ h₂ h₃ h₄ h₅ ?_
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans]

/-- Remove the native unitor identity tails before specializing an identity square. -/
theorem exchangeCoherence_remove_right_id
    {C : Type*} [Category* C] {X Y Z : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z)
    (h : a ≫ (b ≫ 𝟙 Z) = c ≫ 𝟙 Z) : a ≫ b = c := by
  simpa only [Category.comp_id] using h

end CategoryTheory

end OriginalRawArrowNormalization

section OriginalComparisonDiagram

namespace CategoryTheory

/-- Data of a comparison chase. Coherence equations are not fields of this data. -/
structure ExchangeCoherenceDiagram (C : Type*) [Category* C] where
  /-- Common source of the upper route through `p`, `q`, and `b₀`, and the lower
  route through `a` and `m`. -/
  A : C
  /-- First intermediate object on the upper route from `A` to `C₀`. -/
  B : C
  /-- Second intermediate object on the upper route, before the comparison to `D`. -/
  C₀ : C
  /-- Common target in `StartEquation` and source of the next comparison edge `t₂`. -/
  D : C
  /-- Common target of the routes in `FirstTransportEquation` and source of `c₀`. -/
  E : C
  /-- Target of `c₀` and target of the comparison isomorphism `d`. -/
  F : C
  /-- Source of `d` and source of the next upper edge `t₁`. -/
  G : C
  /-- Common target of `t₁` and `s`, and source of the final upper edge `e₀`. -/
  H : C
  /-- Common target of the routes in `FinishEquation`. -/
  I : C
  /-- Target of `a` and source of the lower edges `m` and `b`. -/
  J : C
  /-- Target of `b` and source of the comparison edges `n` and `c`. -/
  K : C
  /-- Target of `c` and source of the comparison edges `r` and `e`. -/
  L : C
  /-- Target of `e` and source of the comparison edges `s` and `z`. -/
  M : C
  /-- Target of `z`, source of `u`, and target of the closing map `τ`. -/
  N : C
  /-- Intermediate object between `N` and the common target `I` on the finishing route. -/
  O : C
  /-- First edge on the upper route from `A` toward `D`. -/
  p : A ⟶ B
  /-- Upper edge from `B` to `C₀` in the initial comparison route. -/
  q : B ⟶ C₀
  /-- Upper edge from `C₀` to `D`, completing the first route of `StartEquation`. -/
  b₀ : C₀ ⟶ D
  /-- Upper comparison edge from `D` to `E` used in `FirstTransportEquation`. -/
  t₂ : D ⟶ E
  /-- Upper edge from `E` to `F`, opposite the target of `d`. -/
  c₀ : E ⟶ F
  /-- Comparison isomorphism from `G` to `F` used to identify the middle route. -/
  d : G ≅ F
  /-- Upper edge from `G` to `H` in `SecondTransportEquation`. -/
  t₁ : G ⟶ H
  /-- Final upper edge from `H` to the common target `I`. -/
  e₀ : H ⟶ I
  /-- Lower edge from `A` to `J`, beginning the source transport route. -/
  a : A ⟶ J
  /-- Edge from `J` to `D`, completing the lower route of `StartEquation`. -/
  m : J ⟶ D
  /-- Lower edge from `J` to `K`, used in the closing transport equation. -/
  b : J ⟶ K
  /-- Edge from `K` to `E`, opposite the route through `m` and `t₂`. -/
  n : K ⟶ E
  /-- Edge from `K` to `L`, beginning the lower route of `MiddleEquation`. -/
  c : K ⟶ L
  /-- Edge from `L` to `G`, whose composite with `d.hom` reaches `F`. -/
  r : L ⟶ G
  /-- Edge from `L` to `M`, used in the closing transport equation. -/
  e : L ⟶ M
  /-- Edge from `M` to `H`, opposite the route through `r` and `t₁`. -/
  s : M ⟶ H
  /-- Edge from `M` to `N`, used in the closing transport equation. -/
  z : M ⟶ N
  /-- Edge from `N` to `O` on the final route to `I`. -/
  u : N ⟶ O
  /-- Edge from `O` to `I`, completing the lower route of `FinishEquation`. -/
  v : O ⟶ I
  /-- Direct closing map from `A` to `N` in `TransportEquation`. -/
  τ : A ⟶ N

namespace ExchangeCoherenceDiagram
variable {C : Type*} [Category* C] (Δ : ExchangeCoherenceDiagram C)

/-- The first comparison square in the shared diagram. -/
def StartEquation : Prop := Δ.p ≫ Δ.q ≫ Δ.b₀ = Δ.a ≫ Δ.m

/-- Transport through the second comparison square. -/
def FirstTransportEquation : Prop := Δ.m ≫ Δ.t₂ = Δ.b ≫ Δ.n

/-- The middle comparison square in the shared diagram. -/
def MiddleEquation : Prop := Δ.n ≫ Δ.c₀ = Δ.c ≫ Δ.r ≫ Δ.d.hom

/-- Transport through the fourth comparison square. -/
def SecondTransportEquation : Prop := Δ.r ≫ Δ.t₁ = Δ.e ≫ Δ.s

/-- The final comparison square in the shared diagram. -/
def FinishEquation : Prop := Δ.s ≫ Δ.e₀ = Δ.z ≫ Δ.u ≫ Δ.v

/-- Closing transport, proved independently by equality elimination. -/
def TransportEquation : Prop := Δ.a ≫ Δ.b ≫ Δ.c ≫ Δ.e ≫ Δ.z = Δ.τ

/-- The conclusion of the comparison chase, not a field or assumed coherence law. -/
def ChainEquation : Prop :=
  Δ.p ≫ Δ.q ≫ Δ.b₀ ≫ Δ.t₂ ≫ Δ.c₀ ≫ Δ.d.inv ≫ Δ.t₁ ≫ Δ.e₀ =
    Δ.τ ≫ Δ.u ≫ Δ.v

/-- The complete chase uses the five comparisons and their proved source transport. -/
theorem chain (h₁ : Δ.StartEquation) (h₂ : Δ.FirstTransportEquation)
    (h₃ : Δ.MiddleEquation) (h₄ : Δ.SecondTransportEquation)
    (h₅ : Δ.FinishEquation) (ht : Δ.TransportEquation) : Δ.ChainEquation :=
  exchangeCoherence_chain (d := Δ.d) h₁ h₂ h₃ h₄ h₅ ht

/-- Evaluate a whole-natural-transformation diagram only after proving its coherence. -/
def app {S T : Type*} [Category* S] [Category* T]
    (Δ : ExchangeCoherenceDiagram (S ⥤ T)) (X : S) : ExchangeCoherenceDiagram T where
  A := Δ.A.obj X
  B := Δ.B.obj X
  C₀ := Δ.C₀.obj X
  D := Δ.D.obj X
  E := Δ.E.obj X
  F := Δ.F.obj X
  G := Δ.G.obj X
  H := Δ.H.obj X
  I := Δ.I.obj X
  J := Δ.J.obj X
  K := Δ.K.obj X
  L := Δ.L.obj X
  M := Δ.M.obj X
  N := Δ.N.obj X
  O := Δ.O.obj X
  p := Δ.p.app X
  q := Δ.q.app X
  b₀ := Δ.b₀.app X
  t₂ := Δ.t₂.app X
  c₀ := Δ.c₀.app X
  d := Δ.d.app X
  t₁ := Δ.t₁.app X
  e₀ := Δ.e₀.app X
  a := Δ.a.app X
  m := Δ.m.app X
  b := Δ.b.app X
  n := Δ.n.app X
  c := Δ.c.app X
  r := Δ.r.app X
  e := Δ.e.app X
  s := Δ.s.app X
  z := Δ.z.app X
  u := Δ.u.app X
  v := Δ.v.app X
  τ := Δ.τ.app X

/-- Component extraction is proved while the whole diagram remains abstract. -/
theorem chain_app {S T : Type*} [Category* S] [Category* T]
    (Δ : ExchangeCoherenceDiagram (S ⥤ T)) (h : Δ.ChainEquation) (X : S) :
    (Δ.app X).ChainEquation := by
  have hc := congrArg (fun η => η.app X) h
  simpa only [ChainEquation, app, NatTrans.comp_app, Iso.app_inv] using hc

end ExchangeCoherenceDiagram

/-- The equality-transport pentagon in an arbitrary whole functor category. -/
theorem exchangeCoherence_whole_transport
    {I C : Type*} [Category* C] (P : I → C)
    {x₀ x₁ x₂ x₃ x₄ x₅ : I}
    (e₁₀ : x₁ = x₀) (e₁₂ : x₁ = x₂) (e₂₃ : x₂ = x₃)
    (e₃₄ : x₃ = x₄) (e₅₄ : x₅ = x₄) (e₀₅ : x₀ = x₅) :
    (eqToIso (congrArg P e₁₀)).inv ≫ (eqToIso (congrArg P e₁₂)).hom ≫
        (eqToIso (congrArg P e₂₃)).hom ≫ (eqToIso (congrArg P e₃₄)).hom ≫
        (eqToIso (congrArg P e₅₄)).inv = (eqToIso (congrArg P e₀₅)).hom := by
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_trans]

section WhiskeredComparisonChain
variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G₁ : A ⥤ B} {G₂ : B ⥤ C} {L₂ : C ⥤ D} {L₁ : B ⥤ E}
  {H₂ : E ⥤ D} {L₀ : A ⥤ F} {H₁ : F ⥤ E}
  {G : A ⥤ C} {M N : A ⥤ E} {P₀ D₀ E₀ N₀ O : A ⥤ D}
  (γ : G ≅ G₁ ⋙ G₂) (δ : M ≅ G₁ ⋙ L₁) (ε : N ≅ L₀ ⋙ H₁)
  (p : P₀ ⟶ G ⋙ L₂) (b₀ : G₁ ⋙ G₂ ⋙ L₂ ⟶ D₀)
  (t₂ : D₀ ⟶ E₀) (c₀ : E₀ ⟶ G₁ ⋙ L₁ ⋙ H₂)
  (t₁ : M ⋙ H₂ ⟶ N ⋙ H₂) (τ : P₀ ⟶ N₀) (u : N₀ ⟶ O)
  (v : O ⟶ L₀ ⋙ H₁ ⋙ H₂)

/-- Shared whole comparison equation retaining the native functor associators. -/
def WhiskeredComparisonChainEquation : Prop :=
  p ≫ (Functor.whiskerRight γ.hom L₂ ≫ (Functor.associator G₁ G₂ L₂).hom) ≫
      b₀ ≫ t₂ ≫ c₀ ≫
      (Functor.isoWhiskerRight δ H₂ ≪≫ Functor.associator G₁ L₁ H₂).inv ≫ t₁ ≫
      (Functor.whiskerRight ε.hom H₂ ≫ (Functor.associator L₀ H₁ H₂).hom) =
    τ ≫ u ≫ v

/-- The component comparison equation with all associator identities removed. -/
def WhiskeredComparisonChainAppEquation (X : A) : Prop :=
  p.app X ≫ L₂.map (γ.hom.app X) ≫ b₀.app X ≫ t₂.app X ≫ c₀.app X ≫
      H₂.map (δ.inv.app X) ≫ t₁.app X ≫ H₂.map (ε.hom.app X) =
    τ.app X ≫ u.app X ≫ v.app X

/-- Remove associator components while all functors and comparison isos are abstract. -/
theorem whiskeredComparisonChain_app
    (h : WhiskeredComparisonChainEquation γ δ ε p b₀ t₂ c₀ t₁ τ u v) (X : A) :
    WhiskeredComparisonChainAppEquation γ δ ε p b₀ t₂ c₀ t₁ τ u v X := by
  have hc := congrArg (fun η => η.app X) h
  simpa only [WhiskeredComparisonChainAppEquation, NatTrans.comp_app, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp] using hc

/-- Extract a literal component equation without reducing any concrete comparison. -/
theorem whiskeredComparisonChain_app_eq (X : A)
    (h : WhiskeredComparisonChainAppEquation γ δ ε p b₀ t₂ c₀ t₁ τ u v X) :
    p.app X ≫ L₂.map (γ.hom.app X) ≫ b₀.app X ≫ t₂.app X ≫ c₀.app X ≫
        H₂.map (δ.inv.app X) ≫ t₁.app X ≫ H₂.map (ε.hom.app X) =
      τ.app X ≫ u.app X ≫ v.app X := h

end WhiskeredComparisonChain

end CategoryTheory

end OriginalComparisonDiagram

section OriginalWholeSquareNormalization

namespace CategoryTheory

section WholeHorizontalSquare
variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G₁ : A ⥤ B} {G₂ : B ⥤ C} {L₂ : C ⥤ D} {L₁ : B ⥤ E}
  {H₂ : E ⥤ D} {L₀ : A ⥤ F} {H₁ : F ⥤ E}
  {G : A ⥤ C} {H : F ⥤ D}
  (α₁ : G₁ ⋙ L₁ ⟶ L₀ ⋙ H₁) (α₂ : G₂ ⋙ L₂ ⟶ L₁ ⋙ H₂)
  (α : G ⋙ L₂ ⟶ L₀ ⋙ H) (γ : G ⟶ G₁ ⋙ G₂) (θ : H ⟶ H₁ ⋙ H₂)

/-- Horizontal square coherence in the whole functor category, with native associators. -/
def WholeHorizontalSquareEquation : Prop :=
  Functor.whiskerRight γ L₂ ≫ (Functor.associator G₁ G₂ L₂).hom ≫
      Functor.whiskerLeft G₁ α₂ ≫ (Functor.associator G₁ L₁ H₂).inv ≫
      Functor.whiskerRight α₁ H₂ ≫ (Functor.associator L₀ H₁ H₂).hom =
    α ≫ Functor.whiskerLeft L₀ θ

/-- Only the final short square is evaluated; no long component chain is exposed. -/
theorem wholeHorizontalSquare_app
    (h : WholeHorizontalSquareEquation α₁ α₂ α γ θ) (X : A) :
    HorizontalSquareEquation (TwoSquare.mk _ _ _ _ α₁) (TwoSquare.mk _ _ _ _ α₂)
      (TwoSquare.mk _ _ _ _ α) γ θ X := by
  have hc := congrArg (fun η => η.app X) h
  simpa only [HorizontalSquareEquation, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using hc

end WholeHorizontalSquare

section WholeNormalization
variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G₁ : A ⥤ B} {G₂ : B ⥤ C} {L₂ : C ⥤ D} {L₁ : B ⥤ E}
  {H₂ : E ⥤ D} {L₀ : A ⥤ F} {H₁ : F ⥤ E}
  {G : A ⥤ C} {H : F ⥤ D} {M N : A ⥤ E}
  {Q R : B ⥤ D} {P T : A ⥤ D}
  (γ : G ≅ G₁ ⋙ G₂) (θ : H ≅ H₁ ⋙ H₂)
  (p : P ≅ G ⋙ L₂) (b : Q ≅ G₂ ⋙ L₂) (t₂ : Q ≅ R) (c : R ≅ L₁ ⋙ H₂)
  (d : M ≅ G₁ ⋙ L₁) (t₁ : M ≅ N) (e : N ≅ L₀ ⋙ H₁)
  (τ : P ≅ T) (u : T ≅ L₀ ⋙ H)
  (α₁ : G₁ ⋙ L₁ ≅ L₀ ⋙ H₁) (α₂ : G₂ ⋙ L₂ ≅ L₁ ⋙ H₂)
  (α : G ⋙ L₂ ≅ L₀ ⋙ H)

/-- Normalize the entire native comparison chain before taking any component. -/
theorem exchangeCoherence_normalize_whole
    (h₁ : α₁ = d.symm ≪≫ t₁ ≪≫ e)
    (h₂ : α₂ = b.symm ≪≫ t₂ ≪≫ c)
    (h : α = p.symm ≪≫ τ ≪≫ u)
    (hc : WhiskeredComparisonChainEquation γ d e p.hom
      (Functor.whiskerLeft G₁ b.inv) (Functor.whiskerLeft G₁ t₂.hom)
      (Functor.whiskerLeft G₁ c.hom) (Functor.whiskerRight t₁.hom H₂)
      τ.hom u.hom (Functor.whiskerLeft L₀ θ.hom)) :
    WholeHorizontalSquareEquation α₁.hom α₂.hom α.hom γ.hom θ.hom := by
  subst α₁
  subst α₂
  subst α
  have hc' := (Iso.eq_inv_comp p).mpr hc
  simpa only [WholeHorizontalSquareEquation, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_comp,
    Functor.whiskerRight_comp, Category.assoc] using hc'

end WholeNormalization

end CategoryTheory

end OriginalWholeSquareNormalization
