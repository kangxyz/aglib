/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Actual fixed-fibre Hom equivalences and split-base pullback arrows

All constructions retain the specified square, its actual projections and the
original chosen pullbacks. The native pullback equivalence is the specified-square
construction specialized to the flipped original square.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A specified cartesian square gives the actual bijection on points over a
fixed base point, by its universal property and original projections. -/
def cartesianPointOverEquiv {C : Type*} [Category* C] {T X Y Z P : C}
    (a : T ⟶ X) (b : T ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback a b f g) (p : P ⟶ Y) :
    {t : P ⟶ T // t ≫ b = p} ≃ {x : P ⟶ X // x ≫ f = p ≫ g} where
  toFun t := ⟨t.val ≫ a, by
    rw [Category.assoc, h.w, ← Category.assoc, t.property]⟩
  invFun x := ⟨h.lift x.val p x.property, h.lift_snd _ _ _⟩
  left_inv t := by
    apply Subtype.ext
    apply h.hom_ext
    · exact h.lift_fst _ _ _
    · exact (h.lift_snd _ _ _).trans t.property.symm
  right_inv x := Subtype.ext (h.lift_fst _ _ _)

/-- Transport actual points with their original base triangle through an isomorphism. -/
def pointOverEquivOfIso {C : Type*} [Category* C] {P Z Y S : C}
    (e : Z ≅ Y) (a : Z ⟶ S) (p : Y ⟶ S) (h : e.hom ≫ p = a) (b : P ⟶ S) :
    {q : P ⟶ Z // q ≫ a = b} ≃ {q : P ⟶ Y // q ≫ p = b} where
  toFun q := ⟨q.val ≫ e.hom, by rw [Category.assoc, h]; exact q.property⟩
  invFun q := ⟨q.val ≫ e.inv, by
    rw [← h]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using q.property⟩
  left_inv q := by
    apply Subtype.ext
    simp only [Category.assoc, e.hom_inv_id, Category.comp_id]
  right_inv q := by
    apply Subtype.ext
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- The pullback universal property identifies the actual geometric fibres,
not merely their sets of topological supports. -/
def pullbackPointOverEquiv {C : Type*} [Category* C] {P B X S : C}
    (f : B ⟶ S) (g : X ⟶ S) [HasPullback f g] (b : P ⟶ B) :
    {t : P ⟶ pullback f g // t ≫ pullback.fst f g = b} ≃
      {q : P ⟶ X // q ≫ g = b ≫ f} :=
  cartesianPointOverEquiv (pullback.snd f g) (pullback.fst f g) g f
    (IsPullback.of_hasPullback f g).flip b

/-- The chosen-pullback specialization keeps the literal forward projection. -/
@[simp]
theorem pullbackPointOverEquiv_apply_val {C : Type*} [Category* C] {P B X S : C}
    (f : B ⟶ S) (g : X ⟶ S) [HasPullback f g] (b : P ⟶ B)
    (t : {t : P ⟶ pullback f g // t ≫ pullback.fst f g = b}) :
    (pullbackPointOverEquiv f g b t).val = t.val ≫ pullback.snd f g := rfl

/-- Its inverse is exactly the original native pullback lift. -/
@[simp]
theorem pullbackPointOverEquiv_symm_apply_val {C : Type*} [Category* C] {P B X S : C}
    (f : B ⟶ S) (g : X ⟶ S) [HasPullback f g] (b : P ⟶ B)
    (q : {q : P ⟶ X // q ≫ g = b ≫ f}) :
    ((pullbackPointOverEquiv f g b).symm q).val =
      pullback.lift b q.val q.property.symm := by
  change (IsPullback.of_hasPullback f g).flip.lift q.val b q.property = _
  apply pullback.hom_ext
  · exact ((IsPullback.of_hasPullback f g).flip.lift_snd _ _ _).trans
      (pullback.lift_fst _ _ _).symm
  · exact ((IsPullback.of_hasPullback f g).flip.lift_fst _ _ _).trans
      (pullback.lift_snd _ _ _).symm

/-- Equality of specified base points changes only the triangle proof. -/
def pointOverEquivOfBaseEq {C : Type*} [Category* C] {P X S : C}
    (f : X ⟶ S) {s t : P ⟶ S} (h : s = t) :
    {q : P ⟶ X // q ≫ f = s} ≃ {q : P ⟶ X // q ≫ f = t} where
  toFun q := ⟨q.val, q.property.trans h⟩
  invFun q := ⟨q.val, q.property.trans h.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport the point-extension bijection across the actual pullback universal property. -/
theorem bijective_over_precomp_of_pullback {C : Type*} [Category* C]
    {P Q X S : C} (f : X ⟶ S) (ξ : P ⟶ S) (e : Q ⟶ P) [HasPullback f ξ]
    (hb : Function.Bijective
      (fun s : Over.mk (𝟙 P) ⟶ Over.mk (pullback.snd f ξ) =>
        (Over.homMk e (Category.comp_id e) : Over.mk e ⟶ Over.mk (𝟙 P)) ≫ s)) :
    Function.Bijective
      (fun s : Over.mk ξ ⟶ Over.mk f =>
        (Over.homMk e rfl : Over.mk (e ≫ ξ) ⟶ Over.mk ξ) ≫ s) := by
  constructor
  · intro p q h
    let p₀ : Over.mk (𝟙 P) ⟶ Over.mk (pullback.snd f ξ) :=
      Over.homMk (pullback.lift p.left (𝟙 _) (by simpa using p.w))
        (pullback.lift_snd _ _ _)
    let q₀ : Over.mk (𝟙 P) ⟶ Over.mk (pullback.snd f ξ) :=
      Over.homMk (pullback.lift q.left (𝟙 _) (by simpa using q.w))
        (pullback.lift_snd _ _ _)
    have h₀ : (Over.homMk e (Category.comp_id e) : Over.mk e ⟶ Over.mk (𝟙 P)) ≫ p₀ =
        (Over.homMk e (Category.comp_id e) : Over.mk e ⟶ Over.mk (𝟙 P)) ≫ q₀ := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · have h' := congrArg (fun k => k.left) h
        simpa [p₀, q₀, Category.assoc, pullback.lift_fst, pullback.lift_snd] using h'
      · simp [p₀, q₀, Category.assoc, pullback.lift_snd]
    have he := congrArg (fun k => k.left ≫ pullback.fst f ξ) (hb.1 h₀)
    apply Over.OverMorphism.ext
    simpa [p₀, q₀, pullback.lift_fst] using he
  · intro p
    let p₀ : Over.mk e ⟶ Over.mk (pullback.snd f ξ) :=
      Over.homMk (pullback.lift p.left e p.w) (pullback.lift_snd _ _ _)
    obtain ⟨s, hs⟩ := hb.2 p₀
    have hsw : s.left ≫ pullback.snd f ξ = 𝟙 P := s.w
    have hq : (s.left ≫ pullback.fst f ξ) ≫ f = ξ := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsw]
      exact Category.id_comp ξ
    refine ⟨Over.homMk (s.left ≫ pullback.fst f ξ) hq, ?_⟩
    apply Over.OverMorphism.ext
    have he := congrArg (fun k => k.left ≫ pullback.fst f ξ) hs
    simpa [p₀, Category.assoc, pullback.lift_fst] using he

end CategoryTheory

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category* C] {S X Y T : C}
  {f : X ⟶ S} {t : T ⟶ S} {r : Y ⟶ X} {p : Y ⟶ T}
  (h : IsPullback r p f t) (b : S ⟶ T) (hb : b ≫ t = 𝟙 S)

/-- The original lift associated with a split base arrow. -/
def splitBaseArrow : X ⟶ Y :=
  h.lift (𝟙 X) (f ≫ b) (by simp [Category.assoc, hb])

@[reassoc (attr := simp)]
theorem splitBaseArrow_fst : h.splitBaseArrow b hb ≫ r = 𝟙 X :=
  h.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem splitBaseArrow_snd : h.splitBaseArrow b hb ≫ p = f ≫ b :=
  h.lift_snd _ _ _

/-- The same two projection laws determine the original split-base lift. -/
theorem eq_splitBaseArrow (a : X ⟶ Y) (haX : a ≫ r = 𝟙 X)
    (haT : a ≫ p = f ≫ b) : a = h.splitBaseArrow b hb :=
  h.hom_ext (haX.trans (h.splitBaseArrow_fst b hb).symm)
    (haT.trans (h.splitBaseArrow_snd b hb).symm)

/-- Every actual arrow into the split fibre factors through the original lift. -/
theorem comp_splitBaseArrow_eq {W : C} (a : W ⟶ Y) (v : W ⟶ S)
    (ha : a ≫ p = v ≫ b) : (a ≫ r) ≫ h.splitBaseArrow b hb = a := by
  apply h.hom_ext
  · simp only [Category.assoc, splitBaseArrow_fst, Category.comp_id]
  · have hstruct : a ≫ r ≫ f = v := by
      calc
        a ≫ r ≫ f = a ≫ p ≫ t := by rw [h.w]
        _ = v ≫ b ≫ t := by rw [← Category.assoc, ha, Category.assoc]
        _ = v := by rw [hb, Category.comp_id]
    calc
      ((a ≫ r) ≫ h.splitBaseArrow b hb) ≫ p = (a ≫ r ≫ f) ≫ b := by
        simp only [Category.assoc, splitBaseArrow_snd]
      _ = v ≫ b := congrArg (fun q => q ≫ b) hstruct
      _ = a ≫ p := ha.symm

/-- The split-base lift exhibits the original Cartesian fibre. -/
theorem isPullback_splitBaseArrow : IsPullback (h.splitBaseArrow b hb) f p b := by
  have hout : IsPullback (h.splitBaseArrow b hb ≫ r) f f (b ≫ t) := by
    rw [splitBaseArrow_fst, hb]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact hout.of_right (h.splitBaseArrow_snd b hb) h

end CategoryTheory.IsPullback
