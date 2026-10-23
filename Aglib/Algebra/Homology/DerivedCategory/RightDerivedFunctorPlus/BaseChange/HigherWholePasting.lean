/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherHorizontalEdges

/-! # Five-edge transport with a shared whole-functor diagram

The data contain only actual objects, arrows, and comparison isomorphisms.
Every compatibility is a separate premise supplied by native witnesses.
-/

@[expose] public section
namespace CategoryTheory

/-- Two five-edge paths and their specified vertex comparisons. -/
structure HigherPastingLadder (C : Type*) [Category* C] where
  /-- Initial vertex of the original three-edge path and comparison path. -/
  A : C
  /-- First intermediate vertex on the original path from `A` to `D`. -/
  B : C
  /-- Second intermediate vertex on the original path from `A` to `D`. -/
  C₀ : C
  /-- Common terminal vertex of both original paths. -/
  D : C
  /-- Intermediate vertex on the original comparison path from `A` to `D`. -/
  T : C
  /-- Comparison-path vertex corresponding to `A`. -/
  A' : C
  /-- Comparison-path vertex corresponding to `B`. -/
  B' : C
  /-- Comparison-path vertex corresponding to `C₀`. -/
  C' : C
  /-- Comparison-path vertex corresponding to `D`. -/
  D' : C
  /-- Comparison-path vertex corresponding to `T`. -/
  T' : C
  /-- First arrow on the original path from `A` to `D`. -/
  a : A ⟶ B
  /-- Second arrow on the original path, from `B` to `C₀`. -/
  b : B ⟶ C₀
  /-- Final arrow on the original path, from `C₀` to `D`. -/
  c : C₀ ⟶ D
  /-- First arrow on the original comparison path from `A` through `T`. -/
  d : A ⟶ T
  /-- Final arrow on the original comparison path from `T` to `D`. -/
  e : T ⟶ D
  /-- First arrow on the comparison path from `A'` to `B'. -/
  a' : A' ⟶ B'
  /-- Second arrow on the comparison path from `B'` to `C'. -/
  b' : B' ⟶ C'
  /-- Final arrow on the comparison path from `C'` to `D'. -/
  c' : C' ⟶ D'
  /-- First arrow on the comparison path from `A'` to `T'. -/
  d' : A' ⟶ T'
  /-- Final arrow on the comparison path from `T'` to `D'. -/
  e' : T' ⟶ D'
  /-- Vertex isomorphism from `A'` to `A`. -/
  iA : A' ≅ A
  /-- Vertex isomorphism from `B'` to `B`. -/
  iB : B' ≅ B
  /-- Vertex isomorphism from `C'` to `C₀`. -/
  iC : C' ≅ C₀
  /-- Vertex isomorphism from `D'` to `D`. -/
  iD : D' ≅ D
  /-- Vertex isomorphism from `T'` to `T`. -/
  iT : T' ≅ T

namespace HigherPastingLadder
variable {C : Type*} [Category* C] (L : HigherPastingLadder C)

/-- Compatibility of the first comparison arrow with the source vertices. -/
def SourceEquation : Prop := L.a' ≫ L.iB.hom = L.iA.hom ≫ L.a
/-- Compatibility of the first edges on the two paths. -/
def FirstEquation : Prop := L.b' ≫ L.iC.hom = L.iB.hom ≫ L.b
/-- Compatibility of the middle edges on the two paths. -/
def SecondEquation : Prop := L.c' ≫ L.iD.hom = L.iC.hom ≫ L.c
/-- Compatibility of the arrows leaving the two source vertices. -/
def OuterEquation : Prop := L.d' ≫ L.iT.hom = L.iA.hom ≫ L.d
/-- Compatibility of the final edges at the common target. -/
def TargetEquation : Prop := L.e' ≫ L.iD.hom = L.iT.hom ≫ L.e
/-- Equality of the two original paths from `A` to `D`. -/
def DerivedEquation : Prop := L.a ≫ L.b ≫ L.c = L.d ≫ L.e
/-- Equality of the two comparison paths from `A'` to `D'. -/
def HigherEquation : Prop := L.a' ≫ L.b' ≫ L.c' = L.d' ≫ L.e'

/-- Transport the already proved derived law using five native comparison edges. -/
theorem pasting
    (ha : L.SourceEquation) (hb : L.FirstEquation) (hc : L.SecondEquation)
    (hd : L.OuterEquation) (he : L.TargetEquation) (hp : L.DerivedEquation) :
    L.HigherEquation := by
  change L.a' ≫ L.b' ≫ L.c' = L.d' ≫ L.e'
  change L.a' ≫ L.iB.hom = L.iA.hom ≫ L.a at ha
  change L.b' ≫ L.iC.hom = L.iB.hom ≫ L.b at hb
  change L.c' ≫ L.iD.hom = L.iC.hom ≫ L.c at hc
  change L.d' ≫ L.iT.hom = L.iA.hom ≫ L.d at hd
  change L.e' ≫ L.iD.hom = L.iT.hom ≫ L.e at he
  change L.a ≫ L.b ≫ L.c = L.d ≫ L.e at hp
  apply (cancel_mono L.iD.hom).mp
  simp only [Category.assoc]
  rw [hc, ← Category.assoc L.b', hb, Category.assoc,
    ← Category.assoc L.a', ha, Category.assoc,
    he, ← Category.assoc L.d', hd, Category.assoc, hp]

/-- Extract only the final short component equation, never the comparison chase. -/
theorem pasting_app {K E : Type*} [Category* K] [Category* E]
    (L : HigherPastingLadder (K ⥤ E)) (h : L.HigherEquation) (F : K) :
    L.a'.app F ≫ L.b'.app F ≫ L.c'.app F = L.d'.app F ≫ L.e'.app F :=
  congrArg (fun η => η.app F) h

end HigherPastingLadder
end CategoryTheory

namespace CategoryTheory

/-- Cancel the native target comparison in the category of whole functors. -/
theorem nativeTransport_target_inverse
    {C : Type*} [Category* C] {A B D E : C}
    (s : A ≅ B) (t : D ≅ E) (m : B ⟶ D) (b : A ⟶ E)
    (hb : b = s.hom ≫ m ≫ t.hom) : b ≫ t.inv = s.hom ≫ m := by
  rw [hb]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The second transported edge uses exchange naturality and the original
single coefficient comparison, independently of any pasting equation. -/
theorem mapped_horizontal_second_edge
    {C D₁ D₂ A₁ A₂ : Type*}
    [Category* C] [Category* D₁] [Category* D₂] [Category* A₁] [Category* A₂]
    (H₁ : D₁ ⥤ A₁) (H₂ : D₂ ⥤ A₂) (G : A₁ ⥤ A₂) (DG : D₁ ⥤ D₂)
    (γ : DG ⋙ H₂ ≅ H₁ ⋙ G) (R : C ⥤ D₁) (Q : C ⥤ D₂)
    (β : R ⋙ DG ⟶ Q) {X Y : C} (p : Y ⟶ X)
    {V : A₁} (iV : V ≅ H₁.obj (R.obj X)) (iE : V ≅ H₁.obj (R.obj Y))
    (iS : G.obj V ≅ H₂.obj (DG.obj (R.obj Y)))
    (ht : iV.hom = iE.hom ≫ H₁.map (R.map p))
    (hs : iS.hom = G.map iE.hom ≫ γ.inv.app (R.obj Y))
    {W : A₂} (iW : W ≅ H₂.obj (Q.obj Y)) (b : G.obj V ⟶ W)
    (hb : b ≫ iW.hom = iS.hom ≫ H₂.map (β.app Y)) :
    b ≫ (iW.hom ≫ H₂.map (Q.map p)) =
      (G.map iV.hom ≫ γ.inv.app (R.obj X)) ≫ H₂.map (β.app X) := by
  have hm : G.map iV.hom ≫ γ.inv.app (R.obj X) =
      iS.hom ≫ H₂.map (DG.map (R.map p)) := by
    have hn := γ.inv.naturality (R.map p)
    simp only [Functor.comp_map] at hn
    rw [ht, G.map_comp, Category.assoc, hn, hs, Category.assoc]
  rw [hm]
  exact mapped_horizontal_single_edge H₂ β p iS iW b hb

/-- Pullback of a whole actual exchange factor through the native homology NatIso. -/
theorem mapped_horizontal_first_whole
    {K D₁ D₂ A₁ A₂ : Type*}
    [Category* K] [Category* D₁] [Category* D₂] [Category* A₁] [Category* A₂]
    (H₁ : D₁ ⥤ A₁) (H₂ : D₂ ⥤ A₂) (G : A₁ ⥤ A₂) (DG : D₁ ⥤ D₂)
    (γ : DG ⋙ H₂ ≅ H₁ ⋙ G) {U V : K ⥤ D₁} (β : U ⟶ V)
    {U' V' : K ⥤ A₁} (iU : U' ≅ U ⋙ H₁) (iV : V' ≅ V ⋙ H₁)
    (b : U' ⟶ V') (hb : b ≫ iV.hom = iU.hom ≫ Functor.whiskerRight β H₁) :
    Functor.whiskerRight b G ≫
        (Functor.whiskerRight iV.hom G ≫ Functor.whiskerLeft V γ.inv) =
      (Functor.whiskerRight iU.hom G ≫ Functor.whiskerLeft U γ.inv) ≫
        Functor.whiskerRight (Functor.whiskerRight β DG) H₂ := by
  apply NatTrans.ext
  funext F
  exact mapped_horizontal_pullback_edge H₁ H₂ G DG γ (β.app F)
    (iU.app F) (iV.app F) (b.app F) (congrArg (fun τ => τ.app F) hb)

/-- The whole second edge retains the coefficient NatIso and native exchange. -/
theorem mapped_horizontal_second_whole
    {K C D₁ D₂ A₁ A₂ : Type*}
    [Category* K] [Category* C] [Category* D₁] [Category* D₂]
    [Category* A₁] [Category* A₂]
    (H₁ : D₁ ⥤ A₁) (H₂ : D₂ ⥤ A₂) (G : A₁ ⥤ A₂) (DG : D₁ ⥤ D₂)
    (γ : DG ⋙ H₂ ≅ H₁ ⋙ G) (R : C ⥤ D₁) (Q : C ⥤ D₂)
    (β : R ⋙ DG ⟶ Q) {X Y : K ⥤ C} (p : Y ⟶ X)
    {V : K ⥤ A₁} (iV : V ≅ X ⋙ R ⋙ H₁) (iE : V ≅ Y ⋙ R ⋙ H₁)
    (iS : V ⋙ G ≅ Y ⋙ R ⋙ DG ⋙ H₂)
    (ht : iV.hom = iE.hom ≫ Functor.whiskerRight p (R ⋙ H₁))
    (hs : iS.hom = Functor.whiskerRight iE.hom G ≫ Functor.whiskerLeft (Y ⋙ R) γ.inv)
    {W : K ⥤ A₂} (iW : W ≅ Y ⋙ Q ⋙ H₂) (b : V ⋙ G ⟶ W)
    (hb : b ≫ iW.hom = iS.hom ≫ Functor.whiskerRight (Functor.whiskerLeft Y β) H₂) :
    b ≫ (iW.hom ≫ Functor.whiskerRight p (Q ⋙ H₂)) =
      (Functor.whiskerRight iV.hom G ≫ Functor.whiskerLeft (X ⋙ R) γ.inv) ≫
        Functor.whiskerRight (Functor.whiskerLeft X β) H₂ := by
  apply NatTrans.ext
  funext F
  exact mapped_horizontal_second_edge H₁ H₂ G DG γ R Q β (p.app F)
    (iV.app F) (iE.app F) (iS.app F)
    (congrArg (fun τ => τ.app F) ht) (congrArg (fun τ => τ.app F) hs)
    (iW.app F) (b.app F) (congrArg (fun τ => τ.app F) hb)

/-- Assemble a whole comparison edge from its already proved native components. -/
theorem whole_three_edge_of_app
    {K E : Type*} [Category* K] [Category* E]
    {A B C D T : K ⥤ E} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : A ⟶ T) (e : T ⟶ D)
    (h : ∀ F, a.app F ≫ b.app F ≫ c.app F = d.app F ≫ e.app F) :
    a ≫ (b ≫ c) = d ≫ e := by
  apply NatTrans.ext
  funext F
  exact h F

/-- Promote and map the accepted derived law before specializing the higher diagram. -/
theorem whole_mapped_pasting_of_app
    {K D E : Type*} [Category* K] [Category* D] [Category* E] (H : D ⥤ E)
    {A B C V T : K ⥤ D} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ V)
    (d : A ⟶ T) (e : T ⟶ V)
    (h : ∀ F, a.app F ≫ b.app F ≫ c.app F = d.app F ≫ e.app F) :
    Functor.whiskerRight a H ≫ Functor.whiskerRight b H ≫ Functor.whiskerRight c H =
      Functor.whiskerRight d H ≫ Functor.whiskerRight e H := by
  apply NatTrans.ext
  funext F
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp]
    using congrArg H.map (h F)

/-- Native interchange, retaining the two functor associators until abstract normalization. -/
theorem whiskerLeft_right_canonical
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (J : A ⥤ B) {F G : B ⥤ C} (β : F ⟶ G) (H : C ⥤ D) :
    Functor.whiskerRight (Functor.whiskerLeft J β) H =
      Functor.whiskerLeft J (Functor.whiskerRight β H) := by
  calc
    _ = (Functor.associator J F H).hom ≫
        Functor.whiskerLeft J (Functor.whiskerRight β H) ≫
        (Functor.associator J G H).inv := Functor.whiskerRight_left J β H
    _ = _ := by
      apply NatTrans.ext
      funext X
      simp only [NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id]

/-- Native prewhiskering coherence, normalized only with abstract functors. -/
theorem whiskerLeft_comp_canonical
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (J : A ⥤ B) (L : B ⥤ C) {F G : C ⥤ D} (β : F ⟶ G) :
    Functor.whiskerLeft (J ⋙ L) β =
      Functor.whiskerLeft J (Functor.whiskerLeft L β) := by
  symm
  calc
    _ = (Functor.associator J L F).inv ≫
        Functor.whiskerLeft (J ⋙ L) β ≫
        (Functor.associator J L G).hom := Functor.whiskerLeft_twice J L β
    _ = _ := by
      apply NatTrans.ext
      funext X
      simp only [NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id]

/-- Native postwhiskering coherence, normalized before any actual exchange is substituted. -/
theorem whiskerRight_comp_canonical
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {F G : A ⥤ B} (β : F ⟶ G) (L : B ⥤ C) (H : C ⥤ D) :
    Functor.whiskerRight (Functor.whiskerRight β L) H =
      Functor.whiskerRight β (L ⋙ H) := by
  calc
    _ = (Functor.associator F L H).hom ≫
        Functor.whiskerRight β (L ⋙ H) ≫
        (Functor.associator G L H).inv := Functor.whiskerRight_twice L H β
    _ = _ := by
      apply NatTrans.ext
      funext X
      simp only [NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Category.id_comp, Category.comp_id]

/-- The first whole edge in the original prewhisker-after-postwhisker convention. -/
theorem mapped_horizontal_first_canonical
    {K C D₁ D₂ A₁ A₂ : Type*}
    [Category* K] [Category* C] [Category* D₁] [Category* D₂]
    [Category* A₁] [Category* A₂]
    (J : K ⥤ C) (H₁ : D₁ ⥤ A₁) (H₂ : D₂ ⥤ A₂)
    (G : A₁ ⥤ A₂) (DG : D₁ ⥤ D₂) (γ : DG ⋙ H₂ ≅ H₁ ⋙ G)
    {U V : C ⥤ D₁} (β : U ⟶ V)
    {U' V' : K ⥤ A₁} (iU : U' ≅ J ⋙ U ⋙ H₁) (iV : V' ≅ J ⋙ V ⋙ H₁)
    (b : U' ⟶ V')
    (hb : b ≫ iV.hom = iU.hom ≫ Functor.whiskerLeft J (Functor.whiskerRight β H₁)) :
    Functor.whiskerRight b G ≫
        (Functor.whiskerRight iV.hom G ≫ Functor.whiskerLeft (J ⋙ V) γ.inv) =
      (Functor.whiskerRight iU.hom G ≫ Functor.whiskerLeft (J ⋙ U) γ.inv) ≫
        Functor.whiskerLeft J (Functor.whiskerRight (Functor.whiskerRight β DG) H₂) := by
  have hb' : b ≫ iV.hom = iU.hom ≫
      Functor.whiskerRight (Functor.whiskerLeft J β) H₁ := by
    rw [whiskerLeft_right_canonical]
    exact hb
  have h := mapped_horizontal_first_whole H₁ H₂ G DG γ
    (Functor.whiskerLeft J β) iU iV b hb'
  rw [whiskerLeft_right_canonical J β DG,
    whiskerLeft_right_canonical J (Functor.whiskerRight β DG) H₂] at h
  exact h

/-- The second edge keeps the original nested coefficient whisker in its conclusion. -/
theorem mapped_horizontal_second_canonical
    {K C₀ C D₁ D₂ A₁ A₂ : Type*}
    [Category* K] [Category* C₀] [Category* C] [Category* D₁] [Category* D₂]
    [Category* A₁] [Category* A₂]
    (J : K ⥤ C₀) (L : C₀ ⥤ C)
    (H₁ : D₁ ⥤ A₁) (H₂ : D₂ ⥤ A₂) (G : A₁ ⥤ A₂) (DG : D₁ ⥤ D₂)
    (γ : DG ⋙ H₂ ≅ H₁ ⋙ G) (R : C ⥤ D₁) (Q : C ⥤ D₂)
    (β : R ⋙ DG ⟶ Q) {Y : K ⥤ C} (p : Y ⟶ J ⋙ L)
    {V : K ⥤ A₁} (iV : V ≅ (J ⋙ L) ⋙ R ⋙ H₁) (iE : V ≅ Y ⋙ R ⋙ H₁)
    (iS : V ⋙ G ≅ Y ⋙ R ⋙ DG ⋙ H₂)
    (ht : iV.hom = iE.hom ≫ Functor.whiskerRight p (R ⋙ H₁))
    (hs : iS.hom = Functor.whiskerRight iE.hom G ≫ Functor.whiskerLeft (Y ⋙ R) γ.inv)
    {W : K ⥤ A₂} (iW : W ≅ Y ⋙ Q ⋙ H₂) (b : V ⋙ G ⟶ W)
    (hb : b ≫ iW.hom = iS.hom ≫ Functor.whiskerRight (Functor.whiskerLeft Y β) H₂) :
    b ≫ (iW.hom ≫ Functor.whiskerRight p (Q ⋙ H₂)) =
      (Functor.whiskerRight iV.hom G ≫ Functor.whiskerLeft ((J ⋙ L) ⋙ R) γ.inv) ≫
        Functor.whiskerLeft J (Functor.whiskerRight (Functor.whiskerLeft L β) H₂) := by
  have h := mapped_horizontal_second_whole H₁ H₂ G DG γ R Q β p iV iE iS ht hs iW b hb
  rw [whiskerLeft_comp_canonical J L β,
    whiskerLeft_right_canonical J (Functor.whiskerLeft L β) H₂] at h
  exact h

/-- Map the native derived equation using precisely the original coefficient convention. -/
theorem whole_mapped_pasting_single
    {K D E Z : Type*} [Category* K] [Category* D] [Category* E] [Category* Z]
    (J : K ⥤ D) (H : E ⥤ Z)
    {A B C V T : D ⥤ E} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ V)
    (d : A ⟶ T) (e : T ⟶ V)
    (h : ∀ M, a.app M ≫ b.app M ≫ c.app M = d.app M ≫ e.app M) :
    Functor.whiskerLeft J (Functor.whiskerRight a H) ≫
        Functor.whiskerLeft J (Functor.whiskerRight b H) ≫
        Functor.whiskerLeft J (Functor.whiskerRight c H) =
      Functor.whiskerLeft J (Functor.whiskerRight d H) ≫
        Functor.whiskerLeft J (Functor.whiskerRight e H) := by
  have hp := whole_mapped_pasting_of_app H
    (Functor.whiskerLeft J a) (Functor.whiskerLeft J b) (Functor.whiskerLeft J c)
    (Functor.whiskerLeft J d) (Functor.whiskerLeft J e) (fun F => h (J.obj F))
  rw [whiskerLeft_right_canonical J a H, whiskerLeft_right_canonical J b H,
    whiskerLeft_right_canonical J c H, whiskerLeft_right_canonical J d H,
    whiskerLeft_right_canonical J e H] at hp
  exact hp

/-- Pull back the original native source and exchange factors only inside the
abstract coefficient category; concrete consumers supply no whiskered proofs. -/
theorem mapped_horizontal_second_native
    {K B C₀ C D₁ D₂ A₁ A₂ : Type*}
    [Category* K] [Category* B] [Category* C₀] [Category* C]
    [Category* D₁] [Category* D₂] [Category* A₁] [Category* A₂]
    (J : K ⥤ C₀) (L : C₀ ⥤ C) (P : K ⥤ B) (N : B ⥤ C)
    (H₁ : D₁ ⥤ A₁) (H₂ : D₂ ⥤ A₂) (G : A₁ ⥤ A₂) (DG : D₁ ⥤ D₂)
    (γ : DG ⋙ H₂ ≅ H₁ ⋙ G) (R : C ⥤ D₁) (Q : C ⥤ D₂)
    (β : R ⋙ DG ⟶ Q) (p : P ⋙ N ⟶ J ⋙ L)
    {V : B ⥤ A₁} (iV : P ⋙ V ≅ (J ⋙ L) ⋙ R ⋙ H₁)
    (ε : V ≅ N ⋙ R ⋙ H₁) (s : V ⋙ G ≅ N ⋙ R ⋙ DG ⋙ H₂)
    (ht : iV.hom = Functor.whiskerLeft P ε.hom ≫ Functor.whiskerRight p (R ⋙ H₁))
    (hs : s.hom = Functor.whiskerRight ε.hom G ≫ Functor.whiskerLeft (N ⋙ R) γ.inv)
    {W : B ⥤ A₂} (t : W ≅ N ⋙ Q ⋙ H₂) (b : V ⋙ G ⟶ W)
    (hb : b ≫ t.hom = s.hom ≫ Functor.whiskerLeft N (Functor.whiskerRight β H₂)) :
    Functor.whiskerLeft P b ≫
        (Functor.whiskerLeft P t.hom ≫ Functor.whiskerRight p (Q ⋙ H₂)) =
      (Functor.whiskerRight iV.hom G ≫ Functor.whiskerLeft ((J ⋙ L) ⋙ R) γ.inv) ≫
        Functor.whiskerLeft J (Functor.whiskerRight (Functor.whiskerLeft L β) H₂) := by
  have hs' : Functor.whiskerLeft P s.hom =
      Functor.whiskerRight (Functor.whiskerLeft P ε.hom) G ≫
        Functor.whiskerLeft ((P ⋙ N) ⋙ R) γ.inv := by
    apply NatTrans.ext
    funext F
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_obj] using congrArg (fun τ => τ.app (P.obj F)) hs
  have hb' : Functor.whiskerLeft P b ≫ Functor.whiskerLeft P t.hom =
      Functor.whiskerLeft P s.hom ≫
        Functor.whiskerRight (Functor.whiskerLeft (P ⋙ N) β) H₂ := by
    simpa only [Functor.whiskerLeft_comp, ← whiskerLeft_right_canonical,
      ← whiskerLeft_comp_canonical] using congrArg (Functor.whiskerLeft P) hb
  exact mapped_horizontal_second_canonical J L H₁ H₂ G DG γ R Q β p iV
    (Functor.isoWhiskerLeft P ε) (Functor.isoWhiskerLeft P s) ht hs'
    (Functor.isoWhiskerLeft P t) (Functor.whiskerLeft P b) hb'

/-- Reassociate only the abstract source of the comparison whisker, leaving
all actual exchange arrows opaque. -/
theorem whole_second_reassociate
    {A B C D E : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D] [Category* E]
    (J : A ⥤ B) (L : B ⥤ C) (R : C ⥤ D) {M N : D ⥤ E} (γ : M ⟶ N)
    {U V : A ⥤ E} (a : U ⟶ V) (b : U ⟶ J ⋙ L ⋙ R ⋙ M)
    (c : J ⋙ L ⋙ R ⋙ N ⟶ V)
    (h : a = (b ≫ Functor.whiskerLeft ((J ⋙ L) ⋙ R) γ) ≫ c) :
    a = (b ≫ Functor.whiskerLeft (J ⋙ L ⋙ R) γ) ≫ c := by
  have hc : Functor.whiskerLeft ((J ⋙ L) ⋙ R) γ =
      Functor.whiskerLeft (J ⋙ L ⋙ R) γ := by
    apply NatTrans.ext
    funext X
    rfl
  rw [← hc]
  exact h

end CategoryTheory
