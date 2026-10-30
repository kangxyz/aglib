/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Coherence

/-!
# Whole coherence of the original source-square comparisons

The finite constructor retains six independent categories, three families of
functors with fixed endpoints, and the original composition comparisons. Its
transport facets follow from equality elimination. Only the three unrotated
associativity laws are supplied by the client.
-/

@[expose] public noncomputable section

namespace CategoryTheory

/-- The original three factors of a source square. -/
def sourceSquareIso {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D]
    {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ C} {I : C ⥤ D}
    {M N : A ⥤ D} (cM : M ≅ F ⋙ G) (cN : N ≅ H ⋙ I) (t : M ≅ N) :
    F ⋙ G ≅ H ⋙ I :=
  cM.symm ≪≫ t ≪≫ cN

/-- Equality transport of a whole comparison after fixed left whiskering. -/
theorem sourceComparison_whiskerLeft_transport
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {I J : Type*} (T : I → A ⥤ C) (Q : J → B ⥤ C) (post : J → I)
    (G : A ⥤ B) (c : ∀ k, T (post k) ≅ G ⋙ Q k)
    {q₀ q₁ : J} (e : q₀ = q₁) :
    (c q₀).hom ≫ Functor.whiskerLeft G (eqToIso (congrArg Q e)).hom =
      (eqToIso (congrArg T (congrArg post e))).hom ≫ (c q₁).hom := by
  subst q₁
  simp

/-- Equality transport of a whole comparison before fixed right whiskering. -/
theorem sourceComparison_whiskerRight_transport
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    {I J : Type*} (T : I → A ⥤ C) (P : J → A ⥤ B) (pre : J → I)
    (H : B ⥤ C) (c : ∀ k, T (pre k) ≅ P k ⋙ H)
    {p₀ p₁ : J} (e : p₀ = p₁) :
    (c p₀).hom ≫ Functor.whiskerRight (eqToIso (congrArg P e)).hom H =
      (eqToIso (congrArg T (congrArg pre e))).hom ≫ (c p₁).hom := by
  subst p₁
  simp

universe uS₀ vS₀ uS₁ vS₁ uS₂ vS₂ uX₀ vX₀ uX₁ vX₁ uX₂ vX₂ uI₀ uI₁ uI₂

/-- Primitive data for the original finite source-coherence construction.
The data contain neither its fifteen-vertex diagram nor a coherence equation. -/
structure SourceCoherenceData
    (S₀ : Type uS₀) [Category.{vS₀} S₀]
    (S₁ : Type uS₁) [Category.{vS₁} S₁]
    (S₂ : Type uS₂) [Category.{vS₂} S₂]
    (X₀ : Type uX₀) [Category.{vX₀} X₀]
    (X₁ : Type uX₁) [Category.{vX₁} X₁]
    (X₂ : Type uX₂) [Category.{vX₂} X₂]
    (I₀ : Type uI₀) (I₁ : Type uI₁) (I₂ : Type uI₂) where
  /-- The functor from the first source category to the first target category. -/
  F₀ : S₀ ⥤ X₀
  /-- The functor from the middle source category to the middle target category. -/
  F₁ : S₁ ⥤ X₁
  /-- The functor from the last source category to the last target category. -/
  F₂ : S₂ ⥤ X₂
  /-- The first transition between source categories. -/
  G₁ : S₀ ⥤ S₁
  /-- The second transition between source categories. -/
  G₂ : S₁ ⥤ S₂
  /-- The first transition between target categories. -/
  H₁ : X₀ ⥤ X₁
  /-- The second transition between target categories. -/
  H₂ : X₁ ⥤ X₂
  /-- The specified composite transition between the endpoint source categories. -/
  G₁₂ : S₀ ⥤ S₂
  /-- The specified composite transition between the endpoint target categories. -/
  H₁₂ : X₀ ⥤ X₂
  /-- The indexed family of functors between the endpoint categories. -/
  T : I₀ → S₀ ⥤ X₂
  /-- The indexed family of functors from the first source to the middle target. -/
  P : I₁ → S₀ ⥤ X₁
  /-- The indexed family of functors from the middle source to the last target. -/
  Q : I₂ → S₁ ⥤ X₂
  /-- The index map for comparisons with `G₁` followed by a member of `Q`. -/
  post : I₂ → I₀
  /-- The index map for comparisons with a member of `P` followed by `H₂`. -/
  pre : I₁ → I₀
  /-- The index of the initial endpoint comparison. -/
  a₀ : I₀
  /-- The index of the final endpoint comparison. -/
  a₅ : I₀
  /-- The index of the initial comparison in the `P` family. -/
  p₀ : I₁
  /-- The index of the final comparison in the `P` family. -/
  p₁ : I₁
  /-- The index of the initial comparison in the `Q` family. -/
  q₀ : I₂
  /-- The index of the final comparison in the `Q` family. -/
  q₁ : I₂
  first_eq : p₀ = p₁
  second_eq : q₀ = q₁
  start_eq : post q₀ = a₀
  middle_eq : post q₁ = pre p₀
  finish_eq : a₅ = pre p₁
  outer_eq : a₀ = a₅
  /-- The comparison between the specified source transition and its two factors. -/
  cG : G₁₂ ≅ G₁ ⋙ G₂
  /-- The comparison between the specified target transition and its two factors. -/
  cH : H₁₂ ≅ H₁ ⋙ H₂
  /-- The initial endpoint comparison with the composite source transition. -/
  cOuter : T a₀ ≅ G₁₂ ⋙ F₂
  /-- The initial `Q` comparison with the second source transition. -/
  cQ₀ : Q q₀ ≅ G₂ ⋙ F₂
  /-- The final `Q` comparison with the second target transition. -/
  cQ₁ : Q q₁ ≅ F₁ ⋙ H₂
  /-- The initial `P` comparison with the first source transition. -/
  cP₀ : P p₀ ≅ G₁ ⋙ F₁
  /-- The final `P` comparison with the first target transition. -/
  cP₁ : P p₁ ≅ F₀ ⋙ H₁
  /-- The comparisons of the indexed endpoint functors with `G₁` followed by `Q`. -/
  cQ : ∀ k, T (post k) ≅ G₁ ⋙ Q k
  /-- The comparisons of the indexed endpoint functors with `P` followed by `H₂`. -/
  cP : ∀ k, T (pre k) ≅ P k ⋙ H₂
  /-- The final endpoint comparison with the composite target transition. -/
  cFinish : T a₅ ≅ F₀ ⋙ H₁₂

namespace SourceCoherenceData

variable {S₀ : Type uS₀} [Category.{vS₀} S₀]
  {S₁ : Type uS₁} [Category.{vS₁} S₁] {S₂ : Type uS₂} [Category.{vS₂} S₂]
  {X₀ : Type uX₀} [Category.{vX₀} X₀] {X₁ : Type uX₁} [Category.{vX₁} X₁]
  {X₂ : Type uX₂} [Category.{vX₂} X₂]
  {I₀ : Type uI₀} {I₁ : Type uI₁} {I₂ : Type uI₂}
  (d : SourceCoherenceData S₀ S₁ S₂ X₀ X₁ X₂ I₀ I₁ I₂)

/-- All fifteen vertices and all original comparison arrows. -/
def diagram : ExchangeCoherenceDiagram (S₀ ⥤ X₂) where
  A := d.T d.a₀
  B := d.G₁₂ ⋙ d.F₂
  C₀ := d.G₁ ⋙ d.G₂ ⋙ d.F₂
  D := d.G₁ ⋙ d.Q d.q₀
  E := d.G₁ ⋙ d.Q d.q₁
  F := d.G₁ ⋙ d.F₁ ⋙ d.H₂
  G := d.P d.p₀ ⋙ d.H₂
  H := d.P d.p₁ ⋙ d.H₂
  I := d.F₀ ⋙ d.H₁ ⋙ d.H₂
  J := d.T (d.post d.q₀)
  K := d.T (d.post d.q₁)
  L := d.T (d.pre d.p₀)
  M := d.T (d.pre d.p₁)
  N := d.T d.a₅
  O := d.F₀ ⋙ d.H₁₂
  p := d.cOuter.hom
  q := Functor.whiskerRight d.cG.hom d.F₂ ≫
    (Functor.associator d.G₁ d.G₂ d.F₂).hom
  b₀ := Functor.whiskerLeft d.G₁ d.cQ₀.inv
  t₂ := Functor.whiskerLeft d.G₁ (eqToIso (congrArg d.Q d.second_eq)).hom
  c₀ := Functor.whiskerLeft d.G₁ d.cQ₁.hom
  d := Functor.isoWhiskerRight d.cP₀ d.H₂ ≪≫
    Functor.associator d.G₁ d.F₁ d.H₂
  t₁ := Functor.whiskerRight (eqToIso (congrArg d.P d.first_eq)).hom d.H₂
  e₀ := Functor.whiskerRight d.cP₁.hom d.H₂ ≫
    (Functor.associator d.F₀ d.H₁ d.H₂).hom
  a := (eqToIso (congrArg d.T d.start_eq)).inv
  m := (d.cQ d.q₀).hom
  b := (eqToIso (congrArg d.T (congrArg d.post d.second_eq))).hom
  n := (d.cQ d.q₁).hom
  c := (eqToIso (congrArg d.T d.middle_eq)).hom
  r := (d.cP d.p₀).hom
  e := (eqToIso (congrArg d.T (congrArg d.pre d.first_eq))).hom
  s := (d.cP d.p₁).hom
  z := (eqToIso (congrArg d.T d.finish_eq)).inv
  u := d.cFinish.hom
  v := Functor.whiskerLeft d.F₀ d.cH.hom
  τ := (eqToIso (congrArg d.T d.outer_eq)).hom

/-- The original first unrotated associativity law. -/
def StartAssociativity : Prop :=
  (d.cQ d.q₀).hom ≫ Functor.whiskerLeft d.G₁ d.cQ₀.hom =
    (eqToIso (congrArg d.T d.start_eq)).hom ≫ d.cOuter.hom ≫
      Functor.whiskerRight d.cG.hom d.F₂ ≫ (Functor.associator d.G₁ d.G₂ d.F₂).hom

/-- The original middle unrotated associativity law. -/
def MiddleAssociativity : Prop :=
  (d.cQ d.q₁).hom ≫ Functor.whiskerLeft d.G₁ d.cQ₁.hom =
    (eqToIso (congrArg d.T d.middle_eq)).hom ≫ (d.cP d.p₀).hom ≫
      Functor.whiskerRight d.cP₀.hom d.H₂ ≫ (Functor.associator d.G₁ d.F₁ d.H₂).hom

/-- The original final unrotated associativity law. -/
def FinishAssociativity : Prop :=
  d.cFinish.hom ≫ Functor.whiskerLeft d.F₀ d.cH.hom =
    (eqToIso (congrArg d.T d.finish_eq)).hom ≫ (d.cP d.p₁).hom ≫
      Functor.whiskerRight d.cP₁.hom d.H₂ ≫ (Functor.associator d.F₀ d.H₁ d.H₂).hom

/-- The first facet is derived by rotating the original associativity equation. -/
theorem start (h : d.StartAssociativity) : d.diagram.StartEquation :=
  exchangeCoherence_rotate_start _ _ _ _ _ _ _
    (Iso.inv_hom_id _) (Iso.hom_inv_id (Functor.isoWhiskerLeft d.G₁ d.cQ₀)) h.symm

/-- The first transport facet is proved from the same source equality. -/
theorem firstTransport : d.diagram.FirstTransportEquation :=
  sourceComparison_whiskerLeft_transport d.T d.Q d.post d.G₁ d.cQ d.second_eq

/-- The middle facet uses the original unrotated comparison. -/
theorem middle (h : d.MiddleAssociativity) : d.diagram.MiddleEquation := h

/-- The second transport facet is proved from the same source equality. -/
theorem secondTransport : d.diagram.SecondTransportEquation :=
  sourceComparison_whiskerRight_transport d.T d.P d.pre d.H₂ d.cP d.first_eq

/-- The final facet is derived by rotating the original associativity equation. -/
theorem finish (h : d.FinishAssociativity) : d.diagram.FinishEquation :=
  exchangeCoherence_rotate_finish _ _ _ _ (Iso.inv_hom_id _) h.symm

/-- All lower source transports compose to the original outer equality transport. -/
theorem transport : d.diagram.TransportEquation :=
  exchangeCoherence_whole_transport d.T d.start_eq (congrArg d.post d.second_eq)
    d.middle_eq (congrArg d.pre d.first_eq) d.finish_eq d.outer_eq

/-- The complete finite chase, including all six proved facets. -/
theorem chain (hS : d.StartAssociativity) (hM : d.MiddleAssociativity)
    (hF : d.FinishAssociativity) : d.diagram.ChainEquation :=
  d.diagram.chain (d.start hS) d.firstTransport (d.middle hM)
    d.secondTransport (d.finish hF) d.transport

/-- The first source square with its original comparison factors. -/
def firstSquare : d.G₁ ⋙ d.F₁ ≅ d.F₀ ⋙ d.H₁ :=
  sourceSquareIso d.cP₀ d.cP₁ (eqToIso (congrArg d.P d.first_eq))

/-- The second source square with its original comparison factors. -/
def secondSquare : d.G₂ ⋙ d.F₂ ≅ d.F₁ ⋙ d.H₂ :=
  sourceSquareIso d.cQ₀ d.cQ₁ (eqToIso (congrArg d.Q d.second_eq))

/-- The outer source square with its original comparison factors. -/
def outerSquare : d.G₁₂ ⋙ d.F₂ ≅ d.F₀ ⋙ d.H₁₂ :=
  sourceSquareIso d.cOuter d.cFinish (eqToIso (congrArg d.T d.outer_eq))

/-- Whole source-square pasting follows from the constructed diagram and its facets. -/
theorem whole (hS : d.StartAssociativity) (hM : d.MiddleAssociativity)
    (hF : d.FinishAssociativity) :
    WholeHorizontalSquareEquation d.firstSquare.hom d.secondSquare.hom
      d.outerSquare.hom d.cG.hom d.cH.hom :=
  exchangeCoherence_normalize_whole d.cG d.cH d.cOuter d.cQ₀
    (eqToIso (congrArg d.Q d.second_eq)) d.cQ₁ d.cP₀
    (eqToIso (congrArg d.P d.first_eq)) d.cP₁
    (eqToIso (congrArg d.T d.outer_eq)) d.cFinish
    d.firstSquare d.secondSquare d.outerSquare rfl rfl rfl (d.chain hS hM hF)

end SourceCoherenceData

end CategoryTheory
