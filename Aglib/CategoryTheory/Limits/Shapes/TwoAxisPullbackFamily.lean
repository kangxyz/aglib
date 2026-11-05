/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.FiniteCoproductMaps
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Two-axis pullback families and their finite coproduct

A commuting change of both base axes need not itself be Cartesian. The
family obtained by the two actual successive pullbacks is nevertheless the
original family pulled back along its coefficient axis. Finite universal
coproducts assemble these component squares, preserving both projections.
The comparison also retains the Cartesian inclusion of every target component.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Limits.TwoAxisPullbackFamily

universe v u w

variable {C : Type u} [Category.{v} C]
  {A B G Y : C} {p : G ⟶ A} {β : B ⟶ A} {a : Y ⟶ G} {b : Y ⟶ B}
  (H : IsPullback a b p β)
  {A' B' : C} (s : A' ⟶ A) (t : B' ⟶ B) (n : B' ⟶ A')
  (hn : n ≫ s = t ≫ β)
  [HasPullback p s] [HasPullback (pullback.snd p s) n]

include hn in
/-- Pasting the two actual pullbacks gives the original structural square. -/
theorem outerSquare : IsPullback
    (pullback.fst (pullback.snd p s) n ≫ pullback.fst p s)
    (pullback.snd (pullback.snd p s) n) p (t ≫ β) := by
  simpa only [hn] using
    (IsPullback.of_hasPullback (pullback.snd p s) n).paste_horiz
      (IsPullback.of_hasPullback p s)

/-- The map to the specified original Cartesian family, without replacing it
by a second chosen pullback object. -/
def componentMap : pullback (pullback.snd p s) n ⟶ Y :=
  H.lift (pullback.fst (pullback.snd p s) n ≫ pullback.fst p s)
    (pullback.snd (pullback.snd p s) n ≫ t)
    (by rw [(outerSquare s t n hn).w, Category.assoc])

@[reassoc (attr := simp)]
theorem componentMap_fst : componentMap H s t n hn ≫ a =
    pullback.fst (pullback.snd p s) n ≫ pullback.fst p s :=
  H.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem componentMap_snd : componentMap H s t n hn ≫ b =
    pullback.snd (pullback.snd p s) n ≫ t :=
  H.lift_snd _ _ _

/-- The actual component family is Cartesian over the coefficient axis. -/
theorem componentSquare : IsPullback
    (pullback.snd (pullback.snd p s) n) (componentMap H s t n hn) t b := by
  exact ((outerSquare s t n hn).of_right' H).flip

section Family

variable [FinitaryExtensive C] {ι : Type w} [Finite ι]
  {As Bs : ι → C} (s : ∀ i, As i ⟶ A) (t : ∀ i, Bs i ⟶ B)
  (n : ∀ i, Bs i ⟶ As i) (hn : ∀ i, n i ≫ s i = t i ≫ β)
  [∀ i, HasPullback p (s i)]
  [∀ i, HasPullback (pullback.snd p (s i)) (n i)]
  [HasPullback (Sigma.desc t) b]

/-- The whole component coproduct is the original family after the whole
coefficient coproduct change. No Cartesianity of the two-axis change is assumed. -/
theorem wholeSquare : IsPullback
    (Sigma.map (fun i => pullback.snd (pullback.snd p (s i)) (n i)))
    (Sigma.desc (fun i => componentMap H (s i) (t i) (n i) (hn i)))
    (Sigma.desc t) b := by
  have h := (FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct Bs)).isPullback_of_isColimit_right
      t (Sigma.desc t) b
      (fun i => pullback.snd (pullback.snd p (s i)) (n i))
      (fun i => componentMap H (s i) (t i) (n i) (hn i))
      (fun i => componentSquare H (s i) (t i) (n i) (hn i))
      (coproductIsCoproduct (fun i => pullback (pullback.snd p (s i)) (n i)))
      (fun i => by simp)
  convert! h using 1 <;> apply Sigma.hom_ext <;> intro i
  · simp only [Sigma.ι_map]
    simpa only [cofan_mk_inj] using (Cofan.IsColimit.fac
      (coproductIsCoproduct (fun i => pullback (pullback.snd p (s i)) (n i)))
      (fun x => pullback.snd (pullback.snd p (s x)) (n x) ≫ Sigma.ι Bs x) i).symm
  · simp only [Sigma.ι_comp_desc]
    simpa only [cofan_mk_inj] using (Cofan.IsColimit.fac
      (coproductIsCoproduct (fun i => pullback (pullback.snd p (s i)) (n i)))
      (fun i => componentMap H (s i) (t i) (n i) (hn i)) i).symm

/-- The canonical whole-family comparison. -/
def iso : (∐ fun i => pullback (pullback.snd p (s i)) (n i)) ≅
    pullback (Sigma.desc t) b :=
  (wholeSquare H s t n hn).isoPullback

@[reassoc (attr := simp)]
theorem iso_hom_fst : (iso H s t n hn).hom ≫ pullback.fst (Sigma.desc t) b =
    Sigma.map (fun i => pullback.snd (pullback.snd p (s i)) (n i)) :=
  (wholeSquare H s t n hn).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem iso_hom_snd : (iso H s t n hn).hom ≫ pullback.snd (Sigma.desc t) b =
    Sigma.desc (fun i => componentMap H (s i) (t i) (n i) (hn i)) :=
  (wholeSquare H s t n hn).isoPullback_hom_snd

@[reassoc (attr := simp)]
theorem iso_inv_fst : (iso H s t n hn).inv ≫
    Sigma.map (fun i => pullback.snd (pullback.snd p (s i)) (n i)) =
      pullback.fst (Sigma.desc t) b :=
  (wholeSquare H s t n hn).isoPullback_inv_fst

@[reassoc (attr := simp)]
theorem iso_inv_snd : (iso H s t n hn).inv ≫
    Sigma.desc (fun i => componentMap H (s i) (t i) (n i) (hn i)) =
      pullback.snd (Sigma.desc t) b :=
  (wholeSquare H s t n hn).isoPullback_inv_snd

/-- The original target-family map on the whole coefficient pullback. -/
def targetMap : pullback (Sigma.desc t) b ⟶ ∐ fun i => pullback p (s i) :=
  (iso H s t n hn).inv ≫
    Sigma.map (fun i => pullback.fst (pullback.snd p (s i)) (n i))

/-- The assembled target map retains the original family projection. -/
@[reassoc (attr := simp)]
theorem targetMap_over : targetMap H s t n hn ≫
    Sigma.desc (fun i => pullback.fst p (s i)) =
      pullback.snd (Sigma.desc t) b ≫ a := by
  apply (cancel_epi (iso H s t n hn).hom).mp
  calc
    (iso H s t n hn).hom ≫ (targetMap H s t n hn ≫
        Sigma.desc (fun i => pullback.fst p (s i))) =
        Sigma.map (fun i => pullback.fst (pullback.snd p (s i)) (n i)) ≫
          Sigma.desc (fun i => pullback.fst p (s i)) := by
      simp only [targetMap, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = Sigma.desc (fun i => componentMap H (s i) (t i) (n i) (hn i)) ≫ a := by
      apply Sigma.hom_ext
      intro i
      simp only [Sigma.ι_map_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc,
        componentMap_fst]
    _ = (iso H s t n hn).hom ≫ (pullback.snd (Sigma.desc t) b ≫ a) := by
      rw [← Category.assoc, iso_hom_snd]

/-- Inclusion of the original component into the whole coefficient pullback. -/
def componentInclusion (i : ι) : pullback (pullback.snd p (s i)) (n i) ⟶
    pullback (Sigma.desc t) b :=
  Sigma.ι (fun i => pullback (pullback.snd p (s i)) (n i)) i ≫ (iso H s t n hn).hom

@[reassoc (attr := simp)]
theorem componentInclusion_targetMap (i : ι) :
    componentInclusion H s t n hn i ≫ targetMap H s t n hn =
      pullback.fst (pullback.snd p (s i)) (n i) ≫
        Sigma.ι (fun i => pullback p (s i)) i := by
  simp only [componentInclusion, targetMap, Category.assoc,
    Iso.hom_inv_id_assoc, Sigma.ι_map]

@[reassoc (attr := simp)]
theorem componentInclusion_fst (i : ι) :
    componentInclusion H s t n hn i ≫ pullback.fst (Sigma.desc t) b =
      pullback.snd (pullback.snd p (s i)) (n i) ≫ Sigma.ι Bs i := by
  simp only [componentInclusion, Category.assoc, iso_hom_fst, Sigma.ι_map]

@[reassoc (attr := simp)]
theorem componentInclusion_snd (i : ι) :
    componentInclusion H s t n hn i ≫ pullback.snd (Sigma.desc t) b =
      componentMap H (s i) (t i) (n i) (hn i) := by
  simp only [componentInclusion, Category.assoc, iso_hom_snd, Sigma.ι_comp_desc]

/-- Every original target component is Cartesian in the assembled family. -/
theorem targetComponentSquare (i : ι) : IsPullback
    (pullback.fst (pullback.snd p (s i)) (n i))
    (componentInclusion H s t n hn i)
    (Sigma.ι (fun i => pullback p (s i)) i) (targetMap H s t n hn) := by
  have h := (FinitaryExtensive.isPullback_sigmaι_sigmaMap
    (fun i => pullback.fst (pullback.snd p (s i)) (n i)) i).flip
  exact h.of_iso (Iso.refl _) (Iso.refl _) (iso H s t n hn) (Iso.refl _)
    (by simp) (by simp [componentInclusion]) (by simp)
    (by simp [targetMap])

end Family

end CategoryTheory.Limits.TwoAxisPullbackFamily
