/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range

/-!
# Transporting actual cartesian scheme squares

Source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original declaration names, universes, maps and mathematical hypotheses are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.PullbackTransport` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`fc0695b9a21762df59a06169098d12bb4bcbb92dfaded711c1f8806661f3ddbf`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

section AlgebraicGeometry.Scheme.Pullback.OuterTransport

/-! Exact cartesian transport through the common chart and two further
pullbacks. These are universal-property lemmas, without support hypotheses. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Pullback.OuterTransport

variable {P C N G U Z : Scheme.{u}}
  (pC : P ⟶ C) (cN : C ⟶ N) (cG : C ⟶ G)
  (pN : P ⟶ N) (pG : P ⟶ G) (o : U ⟶ N)
  (hc : pC ≫ cN = pN)
  (s : Z ⟶ U) (t : Z ⟶ P)
  (H : IsPullback s t o pN)

/-- The literal common-chart lift of an actual local pullback. -/
def commonLift : Z ⟶ pullback cN o :=
  pullback.lift (t ≫ pC) s (by rw [Category.assoc, hc, H.w])

@[reassoc (attr := simp)] lemma commonLift_fst :
    commonLift pC cN pN o hc s t H ≫ pullback.fst cN o = t ≫ pC :=
  pullback.lift_fst ..
@[reassoc (attr := simp)] lemma commonLift_snd :
    commonLift pC cN pN o hc s t H ≫ pullback.snd cN o = s :=
  pullback.lift_snd ..

lemma commonLift_square :
    IsPullback (commonLift pC cN pN o hc s t H) t (pullback.fst cN o) pC := by
  have K : IsPullback (commonLift pC cN pN o hc s t H ≫ pullback.snd cN o)
      t o (pC ≫ cN) := by simpa only [commonLift_snd, hc] using H
  exact K.of_right (commonLift_fst pC cN pN o hc s t H)
    (IsPullback.of_hasPullback cN o).flip

lemma commonLift_global_square (HG : IsPullback pC (𝟙 P) cG pG) :
    IsPullback (commonLift pC cN pN o hc s t H) t
      (pullback.fst cN o ≫ cG) pG := by
  simpa only [Category.comp_id] using
    (commonLift_square pC cN pN o hc s t H).paste_vert HG

variable {Y : Scheme.{u}} (a : Y ⟶ G) (pY : P ⟶ Y)
  (hp : pY ≫ a = pG)
  (HG : IsPullback pC (𝟙 P) cG pG)

/-- Lift to the retained chart, retaining the original P-projection. -/
def retainedLift : Z ⟶ pullback a (pullback.fst cN o ≫ cG) :=
  pullback.lift (t ≫ pY) (commonLift pC cN pN o hc s t H) (by
    rw [Category.assoc, hp]
    exact (commonLift_global_square pC cN cG pN pG o hc s t H HG).w.symm)

@[reassoc (attr := simp)] lemma retainedLift_fst :
    retainedLift pC cN cG pN pG o hc s t H a pY hp HG ≫
      pullback.fst a (pullback.fst cN o ≫ cG) = t ≫ pY := pullback.lift_fst ..
@[reassoc (attr := simp)] lemma retainedLift_snd :
    retainedLift pC cN cG pN pG o hc s t H a pY hp HG ≫
      pullback.snd a (pullback.fst cN o ≫ cG) = commonLift pC cN pN o hc s t H :=
  pullback.lift_snd ..

lemma retainedLift_square :
    IsPullback (retainedLift pC cN cG pN pG o hc s t H a pY hp HG) t
      (pullback.fst a (pullback.fst cN o ≫ cG)) pY := by
  have K : IsPullback
      (retainedLift pC cN cG pN pG o hc s t H a pY hp HG ≫
        pullback.snd a (pullback.fst cN o ≫ cG)) t
      (pullback.fst cN o ≫ cG) (pY ≫ a) := by
    simpa only [retainedLift_snd, hp] using
      commonLift_global_square pC cN cG pN pG o hc s t H HG
  exact K.of_right (retainedLift_fst pC cN cG pN pG o hc s t H a pY hp HG)
    (IsPullback.of_hasPullback a (pullback.fst cN o ≫ cG)).flip

end AlgebraicGeometry.Scheme.Pullback.OuterTransport

namespace AlgebraicGeometry.Scheme.Pullback.OuterTransport
variable {Z U A B X P : Scheme.{u}}
  {a : U ⟶ A} {b : U ⟶ B} {c : A ⟶ X} {d : B ⟶ X}
  (K : IsPullback a b c d) (l : Z ⟶ A) (t : Z ⟶ P) (p : P ⟶ B)
  (H : IsPullback l t c (p ≫ d))

def squareLift : Z ⟶ U := K.lift l (t ≫ p) (by simpa only [Category.assoc] using H.w)

@[reassoc (attr := simp)] lemma squareLift_fst : squareLift K l t p H ≫ a = l := K.lift_fst ..
@[reassoc (attr := simp)] lemma squareLift_snd : squareLift K l t p H ≫ b = t ≫ p := K.lift_snd ..

lemma squareLift_square : IsPullback (squareLift K l t p H) t b p := by
  have H' : IsPullback (squareLift K l t p H ≫ a) t c (p ≫ d) := by
    simpa only [squareLift_fst] using H
  exact H'.of_right (squareLift_snd K l t p H) K

end AlgebraicGeometry.Scheme.Pullback.OuterTransport

namespace AlgebraicGeometry
/-- Extend a genuine intersection from an open of the second component once
all actual intersection points lie there. No equality of nonreduced supports
is used: the universal property is transported through the open immersion. -/
lemma isPullback_extend_second_open
    {P A B U X : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) (b : U ⟶ B)
    [IsOpenImmersion b] (s : P ⟶ A) (t : P ⟶ U)
    (H : IsPullback s t f (b ≫ g))
    (hs : g ⁻¹' Set.range f ⊆ Set.range b) :
    IsPullback s (t ≫ b) f g := by
  have w : s ≫ f = (t ≫ b) ≫ g := by simpa only [Category.assoc] using H.w
  let r : ∀ q : PullbackCone f g, q.pt ⟶ U := fun q =>
    IsOpenImmersion.lift b q.snd (by
      rintro _ ⟨x, rfl⟩
      apply hs
      refine ⟨q.fst x, ?_⟩
      exact congrArg (fun e => e x) q.condition)
  have hr (q : PullbackCone f g) : r q ≫ b = q.snd := IsOpenImmersion.lift_fac _ _ _
  let lift : ∀ q : PullbackCone f g, q.pt ⟶ P := fun q =>
    H.lift q.fst (r q) (by rw [← Category.assoc, hr]; exact q.condition)
  have hleft (q : PullbackCone f g) : lift q ≫ s = q.fst := H.lift_fst ..
  have hright (q : PullbackCone f g) : lift q ≫ (t ≫ b) = q.snd := by
    dsimp only [lift]
    rw [H.lift_snd_assoc, hr]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk w lift hleft hright (by
    intro q e he₁ he₂
    apply H.hom_ext
    · exact he₁.trans (hleft q).symm
    · apply (cancel_mono b).mp
      simpa only [Category.assoc] using he₂.trans (hright q).symm))
end AlgebraicGeometry

end -- noncomputable section
end AlgebraicGeometry.Scheme.Pullback.OuterTransport

section AlgebraicGeometry.Scheme.Pullback.ChartTransport

/-! Universal-property transport of an actual local end/component intersection
through a proved strict chart isomorphism. All component-side maps are retained. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Pullback.ChartTransport
variable {C F O U L P Y Z Q : Scheme.{u}}
  (i : C ⟶ F) (g : O ⟶ F) (n : O ⟶ U) (e : L ⟶ U)
  (I : pullback i g ≅ pullback n e)
  (hI : I.hom ≫ pullback.fst n e = pullback.snd i g)

def strictBranch : pullback n e ⟶ C := I.inv ≫ pullback.fst i g

include hI in
lemma strictBranch_square : IsPullback (strictBranch i g n e I) (pullback.fst n e) i g := by
  apply (IsPullback.of_hasPullback i g).of_iso I (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [strictBranch]
  · simpa only [Iso.refl_hom, Category.comp_id] using hI.symm
  · simp
  · simp

variable (u : U ⟶ Y) (p : P ⟶ Y) (z : Z ⟶ O) (v : Z ⟶ P) (w : Z ⟶ U)
  (Hlocal : IsPullback w v u p) (pG : P ⟶ F)
  (HG : IsPullback z v g pG) (hn : z ≫ n = w)
  (s : Q ⟶ L) (t : Q ⟶ P) (H : IsPullback s t (e ≫ u) p)

def localPoint : Q ⟶ Z := Hlocal.lift (s ≫ e) t (by simpa only [Category.assoc] using H.w)

@[reassoc (attr := simp)] lemma localPoint_node :
    localPoint e u p v w Hlocal s t H ≫ w = s ≫ e := Hlocal.lift_fst ..
@[reassoc (attr := simp)] lemma localPoint_component :
    localPoint e u p v w Hlocal s t H ≫ v = t := Hlocal.lift_snd ..

lemma localPoint_square :
    IsPullback s (localPoint e u p v w Hlocal s t H) e w := by
  have H' : IsPullback s (localPoint e u p v w Hlocal s t H ≫ v) (e ≫ u) p := by
    simpa only [localPoint_component] using H
  exact H'.of_bot (localPoint_node e u p v w Hlocal s t H).symm Hlocal

def pointToBranch : Q ⟶ pullback n e :=
  pullback.lift (localPoint e u p v w Hlocal s t H ≫ z) s (by
    rw [Category.assoc, hn, localPoint_node])

@[reassoc (attr := simp)] lemma pointToBranch_chart :
    pointToBranch n e u p z v w Hlocal hn s t H ≫ pullback.fst n e =
      localPoint e u p v w Hlocal s t H ≫ z := pullback.lift_fst ..
@[reassoc (attr := simp)] lemma pointToBranch_end :
    pointToBranch n e u p z v w Hlocal hn s t H ≫ pullback.snd n e = s := pullback.lift_snd ..

lemma pointToBranch_square :
    IsPullback (pointToBranch n e u p z v w Hlocal hn s t H)
      (localPoint e u p v w Hlocal s t H) (pullback.fst n e) z := by
  have K : IsPullback
      (pointToBranch n e u p z v w Hlocal hn s t H ≫ pullback.snd n e)
      (localPoint e u p v w Hlocal s t H) e (z ≫ n) := by
    simpa only [pointToBranch_end, hn] using localPoint_square e u p v w Hlocal s t H
  exact K.of_right (pointToBranch_chart n e u p z v w Hlocal hn s t H)
    (IsPullback.of_hasPullback n e).flip

def strictPoint : Q ⟶ C :=
  pointToBranch n e u p z v w Hlocal hn s t H ≫ strictBranch i g n e I

include hI HG in
lemma strictPoint_restricted_square :
    IsPullback (strictPoint i g n e I u p z v w Hlocal hn s t H)
      (localPoint e u p v w Hlocal s t H) i (v ≫ pG) := by
  have K := (pointToBranch_square n e u p z v w Hlocal hn s t H).paste_horiz
    (strictBranch_square i g n e I hI)
  simpa only [strictPoint, HG.w] using K

include hI HG in
lemma strictPoint_square [IsOpenImmersion v]
    (hs : pG ⁻¹' Set.range i ⊆ Set.range v) :
    IsPullback (strictPoint i g n e I u p z v w Hlocal hn s t H) t i pG := by
  have K := AlgebraicGeometry.isPullback_extend_second_open i pG v
    (strictPoint i g n e I u p z v w Hlocal hn s t H)
    (localPoint e u p v w Hlocal s t H)
    (strictPoint_restricted_square i g n e I hI u p z v w Hlocal pG HG hn s t H) hs
  simpa only [localPoint_component] using K

include hI HG hn in
omit Hlocal in
lemma strict_preimage_on_chart (_Hlocal : IsPullback w v u p) :
    (v ≫ pG) ⁻¹' Set.range i = w ⁻¹' Set.range e := by
  rw [← HG.w]
  change z ⁻¹' (g ⁻¹' Set.range i) = w ⁻¹' Set.range e
  rw [← AlgebraicGeometry.Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
    (strictBranch_square i g n e I hI).flip, Scheme.Pullback.range_fst]
  change (z ≫ n) ⁻¹' Set.range e = _
  rw [hn]

end AlgebraicGeometry.Scheme.Pullback.ChartTransport

end -- noncomputable section
end AlgebraicGeometry.Scheme.Pullback.ChartTransport

namespace AlgebraicGeometry.Scheme.Pullback.Transport

lemma exceptional_intersection_postcompose {A B P Z W : Scheme.{u}}
    {s : P ⟶ A} {t : P ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z}
    (H : IsPullback s t f g) (j : Z ⟶ W) [Mono j] :
    IsPullback s t (f ≫ j) (g ≫ j) := by
  have K : IsPullback g (𝟙 B) j (g ≫ j) := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa only [Category.comp_id] using H.paste_vert K

lemma exceptional_intersection_cancel {A B P Z W : Scheme.{u}}
    {s : P ⟶ A} {t : P ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z}
    (j : Z ⟶ W) [Mono j] (H : IsPullback s t (f ≫ j) (g ≫ j)) :
    IsPullback s t f g := by
  have hw : s ≫ f = t ≫ g := by
    apply (cancel_mono j).mp
    simpa only [Category.assoc] using H.w
  have K : IsPullback g (𝟙 B) j (g ≫ j) := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have H' : IsPullback s (t ≫ 𝟙 B) (f ≫ j) (g ≫ j) := by simpa using H
  exact H'.of_bot hw K

end AlgebraicGeometry.Scheme.Pullback.Transport

namespace AlgebraicGeometry.Scheme.Pullback.Transport

lemma compatible_on_pullback_of_square {A B X Q T : Scheme.{u}}
    {i : A ⟶ X} {j : B ⟶ X} {s : Q ⟶ A} {t : Q ⟶ B}
    (H : IsPullback s t i j) (a : A ⟶ T) (b : B ⟶ T)
    (h : s ≫ a = t ≫ b) :
    pullback.fst i j ≫ a = pullback.snd i j ≫ b := by
  rw [← cancel_epi H.isoPullback.hom]
  simpa only [H.isoPullback_hom_fst_assoc, H.isoPullback_hom_snd_assoc] using h

lemma compatible_self {A X T : Scheme.{u}} (i : A ⟶ X) [Mono i] (a : A ⟶ T) :
    pullback.fst i i ≫ a = pullback.snd i i ≫ a := by
  have h : pullback.fst i i = pullback.snd i i := (cancel_mono i).mp pullback.condition
  rw [h]

lemma compatible_flip {A B X T : Scheme.{u}} (i : A ⟶ X) (j : B ⟶ X)
    (a : A ⟶ T) (b : B ⟶ T)
    (h : pullback.fst i j ≫ a = pullback.snd i j ≫ b) :
    pullback.fst j i ≫ b = pullback.snd j i ≫ a := by
  rw [← cancel_epi (pullbackSymmetry i j).hom]
  simpa only [pullbackSymmetry_hom_comp_fst_assoc,
    pullbackSymmetry_hom_comp_snd_assoc] using h.symm

end AlgebraicGeometry.Scheme.Pullback.Transport

namespace AlgebraicGeometry.Scheme.Hom.ActualSpecialFiber

/-- Passing from a closed fibre to its ambient model preserves the actual
intersection fibre product, since the fibre inclusion is a monomorphism. -/
def pullbackCompMonoIso {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (i : S ⟶ T) [Mono i] : pullback (f ≫ i) (g ≫ i) ≅ pullback f g :=
  (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono f g i)).isoPullback.symm

@[reassoc (attr := simp)] theorem pullbackCompMonoIso_hom_fst
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [Mono i] :
    (pullbackCompMonoIso f g i).hom ≫ pullback.fst f g = pullback.fst (f ≫ i) (g ≫ i) :=
  (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono f g i)).isoPullback_inv_fst


end AlgebraicGeometry.Scheme.Hom.ActualSpecialFiber

namespace AlgebraicGeometry.Scheme.Pullback.GenericRestriction.SplitRationalComponents

open AlgebraicGeometry.Scheme.Hom.ActualSpecialFiber (pullbackCompMonoIso)

theorem pullbackCompMono_snd {X Y S T : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [Mono i] :
    (pullbackCompMonoIso f g i).hom ≫ pullback.snd f g = pullback.snd (f ≫ i) (g ≫ i) :=
  (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono f g i)).isoPullback_inv_snd

end AlgebraicGeometry.Scheme.Pullback.GenericRestriction.SplitRationalComponents

namespace AlgebraicGeometry.Scheme.Hom.ActualLocalModel.CyclicComponents

open AlgebraicGeometry.Scheme.Hom.ActualSpecialFiber (pullbackCompMonoIso)

@[reassoc (attr := simp)] theorem pullbackCompMonoIso_hom_snd
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [Mono i] :
    (pullbackCompMonoIso f g i).hom ≫ pullback.snd f g = pullback.snd (f ≫ i) (g ≫ i) :=
  (IsPullback.of_isLimit (pullbackIsPullbackOfCompMono f g i)).isoPullback_inv_snd

end AlgebraicGeometry.Scheme.Hom.ActualLocalModel.CyclicComponents
