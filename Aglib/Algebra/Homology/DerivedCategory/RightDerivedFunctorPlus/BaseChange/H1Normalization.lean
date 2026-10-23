/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Types.Basic
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleSquare

/-!
# Normalization across three isomorphisms

These small categorical proofs isolate cancellation and functor action from
large concrete coefficient categories. Their shared propositions retain the
literal original composite maps.
-/

@[expose] public section

namespace CategoryTheory

universe v u w

variable {C : Type u} [Category.{v} C] {P Q R U Z : C}

/-- The literal arrow equation for a square written using three isomorphisms. -/
def IsoTransportArrowEquation (l : P ≅ Q) (e : P ≅ R) (r : R ≅ U)
    (p : Q ⟶ Z) (q : U ⟶ Z) : Prop :=
  (l.inv ≫ e.hom ≫ r.hom) ≫ q = p

/-- Composition and equality transport imply the original transported square. -/
theorem isoTransportArrowEquation (l : P ≅ Q) (e : P ≅ R) (r : R ≅ U)
    (p : Q ⟶ Z) (q : U ⟶ Z) (a : P ⟶ Z) (b : R ⟶ Z)
    (hl : l.hom ≫ p = a) (hr : r.hom ≫ q = b) (he : e.hom ≫ b = a) :
    IsoTransportArrowEquation l e r p q := by
  dsimp only [IsoTransportArrowEquation]
  rw [Category.assoc, Category.assoc, hr, he, ← hl, Iso.inv_hom_id_assoc]

/-- The literal action of the same original three-isomorphism composite. -/
def FunctorIsoTransportApplyEquation (F : C ⥤ Type w)
    (l : P ≅ Q) (e : P ≅ R) (r : R ≅ U) (y : F.obj Q) (t : F.obj U) : Prop :=
  F.map (l.inv ≫ e.hom ≫ r.hom) y = t

/-- Functorial composition transports representatives across the original square. -/
theorem functorIsoTransportApplyEquation (F : C ⥤ Type w)
    (l : P ≅ Q) (e : P ≅ R) (r : R ≅ U)
    (x : F.obj P) (y : F.obj Q) (z : F.obj R) (t : F.obj U)
    (hl : F.map l.hom x = y) (he : F.map e.hom x = z)
    (hr : F.map r.hom z = t) :
    FunctorIsoTransportApplyEquation F l e r y t := by
  dsimp only [FunctorIsoTransportApplyEquation]
  rw [← hl]
  change (F.map l.hom ≫ F.map (l.inv ≫ e.hom ≫ r.hom)) x = t
  rw [← F.map_comp, Iso.hom_inv_id_assoc, F.map_comp]
  change F.map r.hom (F.map e.hom x) = t
  rw [he, hr]

/-- The actual square arrow is retained instead of being reconstructed at a consumer. -/
def ActualIsoTransportArrowEquation (α : Q ≅ U) (p : Q ⟶ Z) (q : U ⟶ Z) : Prop :=
  α.hom ≫ q = p

/-- Normalize an actual square using a separately supplied canonical decomposition. -/
theorem isoTransportArrowEquation_actual (l : P ≅ Q) (e : P ≅ R) (r : R ≅ U)
    (α : Q ≅ U) (hα : α = l.symm ≪≫ e ≪≫ r)
    (p : Q ⟶ Z) (q : U ⟶ Z) (a : P ⟶ Z) (b : R ⟶ Z)
    (hl : l.hom ≫ p = a) (hr : r.hom ≫ q = b) (he : e.hom ≫ b = a) :
    ActualIsoTransportArrowEquation α p q := by
  subst α
  exact isoTransportArrowEquation l e r p q a b hl hr he

/-- Keep the actual action map opaque while normalizing its canonical iso action. -/
theorem functorIsoTransportApplyEquation_actual (F : C ⥤ Type w)
    (l : P ≅ Q) (e : P ≅ R) (r : R ≅ U)
    (α : Q ≅ U) (hα : α = l.symm ≪≫ e ≪≫ r)
    (m : F.obj Q → F.obj U) (hm : m = F.map α.hom)
    (x : F.obj P) (y : F.obj Q) (z : F.obj R) (t : F.obj U)
    (hl : F.map l.hom x = y) (he : F.map e.hom x = z)
    (hr : F.map r.hom z = t) : m y = t := by
  subst m
  subst α
  exact functorIsoTransportApplyEquation F l e r x y z t hl he hr

/-- An unbundled original action avoids changing its coefficient types through
any concrete-category representation. Only its original composition law is used. -/
theorem mapIsoTransportApplyEquation_actual (obj : C → Type w)
    (map : {A B : C} → (A ⟶ B) → obj A → obj B)
    (map_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (x : obj A),
      map (f ≫ g) x = map g (map f x))
    (l : P ≅ Q) (e : P ≅ R) (r : R ≅ U)
    (α : Q ≅ U) (hα : α = l.symm ≪≫ e ≪≫ r)
    (x : obj P) (y : obj Q) (z : obj R) (t : obj U)
    (hl : map l.hom x = y) (he : map e.hom x = z)
    (hr : map r.hom z = t) : map α.hom y = t := by
  subst α
  change map (l.inv ≫ e.hom ≫ r.hom) y = t
  rw [← hl, ← map_comp, Iso.hom_inv_id_assoc, map_comp, he, hr]

/-- An original action respects an actual arrow square, without reconstructing
any component isomorphism or changing the represented coefficient types. -/
theorem mapSquareApply (obj : C → Type w)
    (map : {A B : C} → (A ⟶ B) → obj A → obj B)
    (map_comp : ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (x : obj A),
      map (f ≫ g) x = map g (map f x))
    (a : P ⟶ Q) (s : Q ⟶ U) (t : P ⟶ R) (b : R ⟶ U)
    (hs : a ≫ s = t ≫ b)
    (x : obj P) (y : obj Q) (z : obj R) (w : obj U)
    (ha : map a x = y) (ht : map t x = z) (hb : map b z = w) :
    map s y = w := by
  rw [← ha, ← map_comp, hs, map_comp, ht, hb]

/-- Cancel a square using its actual inverse arrow and native inverse equation. -/
theorem arrowSquareCancel
    (a : P ⟶ Q) (s : Q ⟶ U) (t : P ⟶ R) (b : R ⟶ U)
    (i : Q ⟶ P) (hi : i ≫ a = 𝟙 Q) (hs : a ≫ s = t ≫ b)
    (p : Q ⟶ Z) (q : U ⟶ Z) (c : P ⟶ Z) (d : R ⟶ Z)
    (ha : a ≫ p = c) (hb : b ≫ q = d) (ht : t ≫ d = c) :
    s ≫ q = p := by
  have hc : a ≫ (s ≫ q) = a ≫ p := by
    rw [← Category.assoc, hs, Category.assoc, hb, ht, ha]
  have hc' := congrArg (fun k => i ≫ k) hc
  simpa only [← Category.assoc, hi, Category.id_comp] using hc'

/-- Constant transport through a native single square, with all maps kept literal.
The four equations are the single square, two naturality equations, and the
underived constant square after applying the single functor. -/
theorem singleSquare_constant_arrow
    {P Q R R' T U U' V W Y Z : C}
    (α : P ⟶ Q) (hf : Q ⟶ R) (hc : R ⟶ R')
    (tg : R' ⟶ T) (cg : T ⟶ Z)
    (vg : P ⟶ U) (vc : U ⟶ U') (tf : U' ⟶ V) (cf : V ⟶ Z)
    (sg : R ⟶ W) (ch : W ⟶ T) (sf : U ⟶ Y) (cv : Y ⟶ V) (sa : Y ⟶ W)
    (hs : α ≫ hf ≫ sg = vg ≫ sf ≫ sa)
    (hn₁ : hc ≫ tg = sg ≫ ch) (hn₂ : vc ≫ tf = sf ≫ cv)
    (hk : sa ≫ ch ≫ cg = cv ≫ cf) :
    α ≫ (hf ≫ hc) ≫ (tg ≫ cg) = (vg ≫ vc) ≫ (tf ≫ cf) := by
  simp only [Category.assoc]
  rw [← Category.assoc hc tg cg, hn₁]
  simp only [Category.assoc]
  rw [← Category.assoc α hf (sg ≫ ch ≫ cg)]
  rw [← Category.assoc (α ≫ hf) sg (ch ≫ cg)]
  rw [show (α ≫ hf) ≫ sg = vg ≫ sf ≫ sa by simpa only [Category.assoc] using hs]
  simp only [Category.assoc]
  rw [hk, ← Category.assoc sf cv cf, ← hn₂]
  simp only [Category.assoc]

/-- Actual chosen comparison arrows are normalized from separately established
factorizations, so no concrete isomorphism construction is unfolded here. -/
theorem singleSquare_constant_arrow_actual
    {P Q R R' T U U' V W Y Z : C}
    (α : P ⟶ Q) (hf : Q ⟶ R) (hc : R ⟶ R')
    (tg : R' ⟶ T) (cg : T ⟶ Z)
    (vg : P ⟶ U) (vc : U ⟶ U') (tf : U' ⟶ V) (cf : V ⟶ Z)
    (sg : R ⟶ W) (ch : W ⟶ T) (sf : U ⟶ Y) (cv : Y ⟶ V) (sa : Y ⟶ W)
    (hs : α ≫ hf ≫ sg = vg ≫ sf ≫ sa)
    (hn₁ : hc ≫ tg = sg ≫ ch) (hn₂ : vc ≫ tf = sf ≫ cv)
    (hk : sa ≫ ch ≫ cg = cv ≫ cf)
    (c : Q ⟶ R') (d : R' ⟶ Z) (e : P ⟶ U') (t : U' ⟶ Z)
    (hc' : c = hf ≫ hc) (hd : d = tg ≫ cg) (he : e = vg ≫ vc)
    (ht : t = tf ≫ cf) :
    α ≫ c ≫ d = e ≫ t := by
  subst c
  subst d
  subst e
  subst t
  simpa only [Category.assoc] using
    singleSquare_constant_arrow α hf hc tg cg vg vc tf cf sg ch sf cv sa hs hn₁ hn₂ hk

section FunctorTransport
universe u' v'
variable {D : Type u'} [Category.{v'} D]

/-- Apply a functor to a supplied binary factorization without unfolding its source. -/
theorem map_factorization (F : C ⥤ D) {X Y Z : C}
    (m : X ⟶ Z) (a : X ⟶ Y) (b : Y ⟶ Z) (hm : m = a ≫ b) :
    F.map m = F.map a ≫ F.map b := by
  rw [hm, F.map_comp]

/-- Map a constant-source square before specializing to a concrete single functor. -/
theorem map_three_two_square (F : C ⥤ D) {P Q R S T : C}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ T) (d : P ⟶ S) (e : S ⟶ T)
    (h : a ≫ b ≫ c = d ≫ e) :
    F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e := by
  simpa only [Functor.map_comp] using congrArg F.map h

end FunctorTransport

end CategoryTheory

noncomputable section

namespace CategoryTheory
universe uA vA wA uB vB wB uC vC wC uD vD wD
variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  [HasDerivedCategory.{wB} B] [EnoughInjectives B]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (H : B ⥤ D) (G : A ⥤ C) (V : C ⥤ D)
  [F.Additive] [H.Additive] [G.Additive] [V.Additive]
  [F.PreservesHomology] [H.PreservesHomology] [G.PreservesHomology] [V.PreservesHomology]
  (αD : G.rightDerivedFunctorPlus ⋙ V.rightDerivedFunctorPlus ⟶
    F.rightDerivedFunctorPlus ⋙ H.rightDerivedFunctorPlus)
  {T : A} {ZB : B} {ZC : C} {ZD : D}
  (cD : F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj T) ≅
    (DerivedCategory.Plus.singleFunctor B 0).obj ZB)
  (dD : G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj T) ≅
    (DerivedCategory.Plus.singleFunctor C 0).obj ZC)
  (eD : V.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj ZC) ≅
    (DerivedCategory.Plus.singleFunctor D 0).obj ZD)
  (tD : H.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj ZB) ≅
    (DerivedCategory.Plus.singleFunctor D 0).obj ZD)

/-- Literal derived constant-source square for the supplied original comparisons. -/
def DerivedConstantSquareEquation : Prop :=
  αD.app ((DerivedCategory.Plus.singleFunctor A 0).obj T) ≫
      H.rightDerivedFunctorPlus.map cD.hom ≫ tD.hom =
    V.rightDerivedFunctorPlus.map dD.hom ≫ eD.hom

/-- Original constant square and native single square determine the actual
constant-source derived square. All rewriting stays at abstract functors. -/
theorem derivedConstantSquareEquation_of_single
    (α : G ⋙ V ⟶ F ⋙ H)
    (c : F.obj T ⟶ ZB) (d : G.obj T ⟶ ZC)
    (e : V.obj ZC ⟶ ZD) (t : H.obj ZB ⟶ ZD)
    (hconst : α.app T ≫ H.map c ≫ t = V.map d ≫ e)
    (hsingle : SingleComparisonSquareEquation F H G V α αD T)
    (hc : cD.hom = (F.rightDerivedFunctorPlusSingleIso 0).hom.app T ≫
      (DerivedCategory.Plus.singleFunctor B 0).map c)
    (hd : dD.hom = (G.rightDerivedFunctorPlusSingleIso 0).hom.app T ≫
      (DerivedCategory.Plus.singleFunctor C 0).map d)
    (he : eD.hom = (V.rightDerivedFunctorPlusSingleIso 0).hom.app ZC ≫
      (DerivedCategory.Plus.singleFunctor D 0).map e)
    (ht : tD.hom = (H.rightDerivedFunctorPlusSingleIso 0).hom.app ZB ≫
      (DerivedCategory.Plus.singleFunctor D 0).map t) :
    DerivedConstantSquareEquation F H G V αD cD dD eD tD := by
  dsimp only [DerivedConstantSquareEquation]
  exact singleSquare_constant_arrow_actual
    (αD.app ((DerivedCategory.Plus.singleFunctor A 0).obj T))
    (H.rightDerivedFunctorPlus.map ((F.rightDerivedFunctorPlusSingleIso 0).hom.app T))
    (H.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor B 0).map c))
    ((H.rightDerivedFunctorPlusSingleIso 0).hom.app ZB)
    ((DerivedCategory.Plus.singleFunctor D 0).map t)
    (V.rightDerivedFunctorPlus.map ((G.rightDerivedFunctorPlusSingleIso 0).hom.app T))
    (V.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor C 0).map d))
    ((V.rightDerivedFunctorPlusSingleIso 0).hom.app ZC)
    ((DerivedCategory.Plus.singleFunctor D 0).map e)
    ((H.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj T))
    ((DerivedCategory.Plus.singleFunctor D 0).map (H.map c))
    ((V.rightDerivedFunctorPlusSingleIso 0).hom.app (G.obj T))
    ((DerivedCategory.Plus.singleFunctor D 0).map (V.map d))
    ((DerivedCategory.Plus.singleFunctor D 0).map (α.app T))
    hsingle
    ((H.rightDerivedFunctorPlusSingleIso 0).hom.naturality c)
    ((V.rightDerivedFunctorPlusSingleIso 0).hom.naturality d)
    (map_three_two_square (DerivedCategory.Plus.singleFunctor D 0) _ _ _ _ _ hconst)
    (H.rightDerivedFunctorPlus.map cD.hom) tD.hom
    (V.rightDerivedFunctorPlus.map dD.hom) eD.hom
    (map_factorization H.rightDerivedFunctorPlus _ _ _ hc) ht
    (map_factorization V.rightDerivedFunctorPlus _ _ _ hd) he
end CategoryTheory
