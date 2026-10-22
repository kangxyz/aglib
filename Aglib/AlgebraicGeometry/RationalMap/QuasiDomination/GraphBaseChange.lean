/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Base change of the actual support of a graph

The canonical map of relative products is open when its base map is open.
An actual factor of a graph target through an open base induces an actual
factor of its pullback through the corresponding open product. Both
projections and the global target inclusion are retained literally. There is
no assertion that schematic images commute with nonflat base change.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {B X Y S G : Scheme.{u}}

/-- The canonical map between the actual relative products. -/
def productBaseChangeMap (q : B ⟶ X) (pX : X ⟶ S) (pY : Y ⟶ S) :
    pullback (q ≫ pX) pY ⟶ pullback pX pY :=
  (pullbackRightPullbackFstIso pX pY q).inv ≫
    pullback.snd q (pullback.fst pX pY)

@[reassoc (attr := simp)]
lemma productBaseChangeMap_fst (q : B ⟶ X) (pX : X ⟶ S) (pY : Y ⟶ S) :
    productBaseChangeMap q pX pY ≫ pullback.fst pX pY =
      pullback.fst (q ≫ pX) pY ≫ q := by
  simp [productBaseChangeMap, Category.assoc]

@[reassoc (attr := simp)]
lemma productBaseChangeMap_snd (q : B ⟶ X) (pX : X ⟶ S) (pY : Y ⟶ S) :
    productBaseChangeMap q pX pY ≫ pullback.snd pX pY =
      pullback.snd (q ≫ pX) pY := by
  simp [productBaseChangeMap, Category.assoc]

instance (q : B ⟶ X) (pX : X ⟶ S) (pY : Y ⟶ S) [IsOpenImmersion q] :
    IsOpenImmersion (productBaseChangeMap q pX pY) := by
  delta productBaseChangeMap
  infer_instance

variable (W : X.Opens) (pX : X ⟶ S) (pY : Y ⟶ S)
    (c : G ⟶ pullback pX pY) (r : G ⟶ W.toScheme)
    (hr : r ≫ W.ι = c ≫ pullback.fst pX pY) (β : B ⟶ X)

/-- The base projection of the pulled-back graph target lifts to the actual
inverse image of the ambient open. -/
def supportedGraphBaseChangeToOpen :
    pullback c (productBaseChangeMap β pX pY) ⟶ pullback β W.ι :=
  pullback.lift
    (pullback.snd c (productBaseChangeMap β pX pY) ≫ pullback.fst (β ≫ pX) pY)
    (pullback.fst c (productBaseChangeMap β pX pY) ≫ r) (by
      calc
        _ = pullback.snd c (productBaseChangeMap β pX pY) ≫
            productBaseChangeMap β pX pY ≫ pullback.fst pX pY := by simp
        _ = pullback.fst c (productBaseChangeMap β pX pY) ≫
            c ≫ pullback.fst pX pY := by
          rw [← Category.assoc, ← pullback.condition, Category.assoc]
        _ = _ := by simp only [Category.assoc, hr])

@[reassoc (attr := simp)]
lemma supportedGraphBaseChangeToOpen_fst :
    supportedGraphBaseChangeToOpen W pX pY c r hr β ≫ pullback.fst β W.ι =
      pullback.snd c (productBaseChangeMap β pX pY) ≫ pullback.fst (β ≫ pX) pY := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma supportedGraphBaseChangeToOpen_snd :
    supportedGraphBaseChangeToOpen W pX pY c r hr β ≫ pullback.snd β W.ι =
      pullback.fst c (productBaseChangeMap β pX pY) ≫ r := by
  exact pullback.lift_snd _ _ _

/-- The actual pulled-back graph target factors through the local ambient
product. For a closed `c`, its global target map is a closed immersion by
base change, exactly as required by `SupportedGraph`. -/
def supportedGraphBaseChangeLift :
    pullback c (productBaseChangeMap β pX pY) ⟶
      pullback (pullback.fst β W.ι ≫ β ≫ pX) pY :=
  pullback.lift (supportedGraphBaseChangeToOpen W pX pY c r hr β)
    (pullback.snd c (productBaseChangeMap β pX pY) ≫ pullback.snd (β ≫ pX) pY) (by
      rw [← Category.assoc, supportedGraphBaseChangeToOpen_fst,
        Category.assoc, pullback.condition, ← Category.assoc])

@[reassoc (attr := simp)]
lemma supportedGraphBaseChangeLift_fst :
    supportedGraphBaseChangeLift W pX pY c r hr β ≫
      pullback.fst (pullback.fst β W.ι ≫ β ≫ pX) pY =
        supportedGraphBaseChangeToOpen W pX pY c r hr β := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma supportedGraphBaseChangeLift_snd :
    supportedGraphBaseChangeLift W pX pY c r hr β ≫
      pullback.snd (pullback.fst β W.ι ≫ β ≫ pX) pY =
        pullback.snd c (productBaseChangeMap β pX pY) ≫ pullback.snd (β ≫ pX) pY := by
  exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma supportedGraphBaseChangeLift_comp :
    supportedGraphBaseChangeLift W pX pY c r hr β ≫
      productBaseChangeMap (pullback.fst β W.ι) (β ≫ pX) pY =
        pullback.snd c (productBaseChangeMap β pX pY) := by
  apply pullback.hom_ext <;> simp [Category.assoc]

end AlgebraicGeometry.Scheme.QuasiDomination
