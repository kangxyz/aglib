/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.ClosedGraphComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Reverse closed graphs over a proper modification

Once the original-base triangle is known, a graph closed over a more distant
base is also closed over the original base. The comparison of the two products
is monic, hence separated, which suffices for closed-immersion cancellation.
Projection along a proper modification then makes the reverse map proper.
Neither density nor separatedness of the original base over the distant base
is needed here; these may be used separately to establish the triangle.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {B X V S W : Scheme.{u}} (β : B ⟶ X) (φ : V ⟶ X)
    (pX : X ⟶ S) (pV : V ⟶ S) (hφ : φ ≫ pX = pV)

/-- The canonical comparison from the product over the original base to the
product over the distant base. Both projections are unchanged. -/
def graphBaseRestrictionMap : pullback β φ ⟶ pullback (β ≫ pX) pV :=
  pullback.lift (pullback.fst β φ) (pullback.snd β φ) (by
    calc
      pullback.fst β φ ≫ (β ≫ pX) = (pullback.fst β φ ≫ β) ≫ pX :=
        (Category.assoc _ _ _).symm
      _ = (pullback.snd β φ ≫ φ) ≫ pX := by rw [pullback.condition]
      _ = pullback.snd β φ ≫ pV := by rw [Category.assoc, hφ])

@[reassoc (attr := simp)]
lemma graphBaseRestrictionMap_fst :
    graphBaseRestrictionMap β φ pX pV hφ ≫ pullback.fst (β ≫ pX) pV =
      pullback.fst β φ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graphBaseRestrictionMap_snd :
    graphBaseRestrictionMap β φ pX pV hφ ≫ pullback.snd (β ≫ pX) pV =
      pullback.snd β φ := pullback.lift_snd _ _ _

instance : Mono (graphBaseRestrictionMap β φ pX pV hφ) where
  right_cancellation {T} a b hab := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, graphBaseRestrictionMap_fst] using
        congrArg (fun k => k ≫ pullback.fst (β ≫ pX) pV) hab
    · simpa only [Category.assoc, graphBaseRestrictionMap_snd] using
        congrArg (fun k => k ≫ pullback.snd (β ≫ pX) pV) hab

include hφ in
/-- The original-base triangle implies the distant-base triangle. -/
lemma reverseGraph_over (j : W ⟶ B) (ψ : W ⟶ V) (w : j ≫ β = ψ ≫ φ) :
    j ≫ (β ≫ pX) = ψ ≫ pV := by
  rw [← Category.assoc, w, Category.assoc, hφ]

include hφ in
/-- A literal reverse graph closed over the distant base remains closed over
the original base. The comparison is separated because it is monic. -/
theorem isClosedImmersion_reverseGraph (j : W ⟶ B) (ψ : W ⟶ V)
    (w : j ≫ β = ψ ≫ φ) (wS : j ≫ (β ≫ pX) = ψ ≫ pV)
    [IsClosedImmersion (pullback.lift j ψ wS)] :
    IsClosedImmersion (pullback.lift j ψ w) := by
  have hgraph : pullback.lift j ψ w ≫ graphBaseRestrictionMap β φ pX pV hφ =
      pullback.lift j ψ wS := by
    apply pullback.hom_ext <;> simp only [Category.assoc,
      graphBaseRestrictionMap_fst, graphBaseRestrictionMap_snd,
      pullback.lift_fst, pullback.lift_snd]
  have : IsClosedImmersion (pullback.lift j ψ w ≫
      graphBaseRestrictionMap β φ pX pV hφ) := by
    rw [hgraph]
    infer_instance
  exact IsClosedImmersion.of_comp _ (graphBaseRestrictionMap β φ pX pV hφ)

include hφ in
/-- A reverse closed graph over a proper ambient modification makes the
actual reverse map proper, without any density premise. -/
theorem isProper_of_reverse_closedGraph [IsProper β]
    (j : W ⟶ B) (ψ : W ⟶ V)
    (w : j ≫ β = ψ ≫ φ) (wS : j ≫ (β ≫ pX) = ψ ≫ pV)
    [IsClosedImmersion (pullback.lift j ψ wS)] : IsProper ψ := by
  have := isClosedImmersion_reverseGraph β φ pX pV hφ j ψ w wS
  have : IsProper (pullback.lift j ψ w ≫ pullback.snd β φ) := inferInstance
  simpa only [pullback.lift_snd] using this

/-- Composing the reverse graph with the original closed graph enlarges the
target while retaining the literal original maps over the distant base. -/
theorem isClosedImmersion_enlargedReverseGraph {Y : Scheme.{u}}
    (pY : Y ⟶ S) (v : V ⟶ Y) (hφY : φ ≫ pX = v ≫ pY)
    [IsClosedImmersion (pullback.lift φ v hφY)]
    (j : W ⟶ B) (ψ : W ⟶ V) (w : j ≫ β = ψ ≫ φ)
    (hw : j ≫ (β ≫ pX) = (ψ ≫ v) ≫ pY)
    [IsClosedImmersion (pullback.lift j ψ w)] :
    IsClosedImmersion (pullback.lift j (ψ ≫ v) hw) := by
  let i := pullback.lift φ v hφY
  have w' : j ≫ β = ψ ≫ (i ≫ pullback.fst pX pY) := by
    simpa only [i, pullback.lift_fst] using w
  have hlift {A B C Z : Scheme.{u}} {a a' : A ⟶ Z} {b b' : B ⟶ Z}
      (ha : a = a') (hb : b = b') (i : C ⟶ A) (k : C ⟶ B)
      (v : i ≫ a = k ≫ b) (v' : i ≫ a' = k ≫ b') :
      pullback.lift i k v' = pullback.lift i k v ≫ (pullback.congrHom ha hb).hom := by
    subst a'
    subst b'
    simp
  have : IsClosedImmersion (pullback.lift j ψ w') := by
    rw [hlift rfl (show φ = i ≫ pullback.fst pX pY from (pullback.lift_fst φ v hφY).symm) j ψ w w']
    infer_instance
  have hw' : j ≫ (β ≫ pX) = (ψ ≫ i ≫ pullback.snd pX pY) ≫ pY := by
    simpa only [i, pullback.lift_snd] using hw
  have H := isClosedImmersion_graph_comp_closedTarget pX pY i β j ψ w' hw'
  simpa only [i, pullback.lift_snd] using H

end AlgebraicGeometry.Scheme.QuasiDomination
