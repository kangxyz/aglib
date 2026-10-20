/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Morphisms and cartesian locality on open source covers

Source: `R5Lab.Aglib.AlgebraicGeometry.Gluing.SourceOpenCover`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `d995f1b8442eef2e27bcdc48173a80b889001d606909130d25a3d9e737f2c345`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

section AlgebraicGeometry.Scheme.SourceOpenCover

/-! Ordinary source-open gluing and cartesian locality.
No geometric premise family is introduced: every cover, map, overlap equality,
chart square, and rectangle square is supplied explicitly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.SourceOpenCover

/-- A cartesian square with identity second projection determines every map
whose base projection factors through that identity chart. -/
lemma eq_comp_of_identity_square {A V B T : Scheme.{u}}
    (j : A ⟶ V) (v : V ⟶ B) (a : A ⟶ B)
    (H : IsPullback j (𝟙 A) v a)
    (f : T ⟶ V) (c : T ⟶ A) (h : f ≫ v = c ≫ a) :
    f = c ≫ j := by
  have hc : H.lift f c h = c := by simpa using H.lift_snd f c h
  simpa only [hc] using (H.lift_fst f c h).symm

section TwoOpens
variable {A B W V : Scheme.{u}} (iA : A ⟶ W) (iB : B ⟶ W)
  [IsOpenImmersion iA] [IsOpenImmersion iB]
  (cover : ∀ w : W, w ∈ Set.range iA ∨ w ∈ Set.range iB)

/-- The ordinary two-open source cover. The false chart is `A`, the true chart is `B`. -/
def twoOpenCover : W.OpenCover :=
  Scheme.Cover.mkOfCovers Bool
    (fun | false => A | true => B)
    (fun | false => iA | true => iB)
    (by
      intro w
      rcases cover w with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact ⟨false, a, ha⟩
      · exact ⟨true, b, hb⟩)
    (by intro b; cases b <;> infer_instance)

variable (a : A ⟶ V) (b : B ⟶ V)
  (overlap : pullback.fst iA iB ≫ a = pullback.snd iA iB ≫ b)

def localMap (k : Bool) : (twoOpenCover iA iB cover).X k ⟶ V :=
  match k with
  | false => a
  | true => b

include overlap in
lemma localMap_compatible (k l : Bool) :
    pullback.fst ((twoOpenCover iA iB cover).f k) ((twoOpenCover iA iB cover).f l) ≫
      localMap iA iB cover a b k =
    pullback.snd _ _ ≫ localMap iA iB cover a b l := by
  cases k <;> cases l
  · change pullback.fst iA iA ≫ a = pullback.snd iA iA ≫ a
    have h : pullback.fst iA iA = pullback.snd iA iA :=
      (cancel_mono iA).mp pullback.condition
    rw [h]
  · exact overlap
  · change pullback.fst iB iA ≫ b = pullback.snd iB iA ≫ a
    simpa only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
      pullbackSymmetry_hom_comp_fst_assoc] using
      congrArg (fun f => (pullbackSymmetry iB iA).hom ≫ f) overlap.symm
  · change pullback.fst iB iB ≫ b = pullback.snd iB iB ≫ b
    have h : pullback.fst iB iB = pullback.snd iB iB :=
      (cancel_mono iB).mp pullback.condition
    rw [h]

/-- Glue actual maps defined on a two-open source cover. -/
def glueTwo : W ⟶ V :=
  (twoOpenCover iA iB cover).glueMorphisms (localMap iA iB cover a b)
    (localMap_compatible iA iB cover a b overlap)

@[reassoc (attr := simp)] lemma left_glueTwo :
    iA ≫ glueTwo iA iB cover a b overlap = a :=
  Scheme.Cover.ι_glueMorphisms (twoOpenCover iA iB cover)
    (localMap iA iB cover a b) (localMap_compatible iA iB cover a b overlap) false

@[reassoc (attr := simp)] lemma right_glueTwo :
    iB ≫ glueTwo iA iB cover a b overlap = b :=
  Scheme.Cover.ι_glueMorphisms (twoOpenCover iA iB cover)
    (localMap iA iB cover a b) (localMap_compatible iA iB cover a b overlap) true

/-- A common contraction descends with the glued map. -/
lemma glueTwo_comp {Z : Scheme.{u}} (v : V ⟶ Z) (w : W ⟶ Z)
    (ha : a ≫ v = iA ≫ w) (hb : b ≫ v = iB ≫ w) :
    glueTwo iA iB cover a b overlap ≫ v = w := by
  apply Scheme.Cover.hom_ext (twoOpenCover iA iB cover)
  intro k
  cases k
  · change iA ≫ (glueTwo iA iB cover a b overlap ≫ v) = iA ≫ w
    simpa only [left_glueTwo_assoc] using ha
  · change iB ≫ (glueTwo iA iB cover a b overlap ≫ v) = iB ≫ w
    simpa only [right_glueTwo_assoc] using hb

end TwoOpens

/-- Cartesian locality on a target open cover, accepting any supplied cartesian
source charts rather than forcing canonical pullback objects into the client API. -/
lemma isPullback_of_openCover_charts
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (b : W ⟶ Y) (v : X ⟶ Z) (t : Y ⟶ Z)
    (U : X.OpenCover) (Wi : U.I₀ → Scheme.{u})
    (si : ∀ i, Wi i ⟶ W) (li : ∀ i, Wi i ⟶ U.X i)
    (chart : ∀ i, IsPullback (li i) (si i) (U.f i) f)
    (rectangle : ∀ i, IsPullback (li i) (si i ≫ b) (U.f i ≫ v) t) :
    IsPullback f b v t := by
  apply Scheme.isPullback_of_openCover f b v t U
  intro i
  let e := (chart i).flip.isoPullback
  change IsPullback (pullback.snd f (U.f i))
    (pullback.fst f (U.f i) ≫ b) (U.f i ≫ v) t
  apply (rectangle i).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [e]
  · simp [e]
  · simp
  · simp

/-- Range equalities and chart triangles construct the source-chart pullback
squares required by cartesian locality. The rectangle squares remain explicit. -/
lemma isPullback_of_openCover_ranges
    {W X Y Z : Scheme.{u}} (f : W ⟶ X) (b : W ⟶ Y) (v : X ⟶ Z) (t : Y ⟶ Z)
    (U : X.OpenCover) (Wi : U.I₀ → Scheme.{u})
    (si : ∀ i, Wi i ⟶ W) (li : ∀ i, Wi i ⟶ U.X i)
    [∀ i, IsOpenImmersion (si i)]
    (triangle : ∀ i, si i ≫ f = li i ≫ U.f i)
    (range : ∀ i, f ⁻¹ᵁ (U.f i).opensRange = (si i).opensRange)
    (rectangle : ∀ i, IsPullback (li i) (si i ≫ b) (U.f i ≫ v) t) :
    IsPullback f b v t := by
  apply isPullback_of_openCover_charts f b v t U Wi si li _ rectangle
  intro i
  exact IsOpenImmersion.isPullback (li i) (si i) (U.f i) f (triangle i) (range i)

end AlgebraicGeometry.Scheme.SourceOpenCover

end -- noncomputable section
end AlgebraicGeometry.Scheme.SourceOpenCover
