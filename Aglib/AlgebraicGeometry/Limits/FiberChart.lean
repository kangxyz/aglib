/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Base change of a chart with its structural triangle

Source: R5 revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original declaration names, universes, maps and mathematical hypotheses are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.FiberChart` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`158f7ba32a2b095653235e6b5f1360b6826efe69b640d4edebf425509cebd39b`.
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

namespace AlgebraicGeometry.Scheme.Pullback.Fibre

/-- Base change of an actual chart, retaining a specified structural triangle. -/
def fibreChart {A Y S T : Scheme.{u}} (j : A ⟶ Y) (a : A ⟶ S)
    (f : Y ⟶ S) (g : T ⟶ S) (h : j ≫ f = a) :
    pullback a g ⟶ pullback f g :=
  (pullback.congrHom h rfl).inv ≫
    (pullbackRightPullbackFstIso f g j).inv ≫ pullback.snd j (pullback.fst f g)

@[reassoc] lemma fibreChart_fst {A Y S T : Scheme.{u}} (j : A ⟶ Y) (a : A ⟶ S)
    (f : Y ⟶ S) (g : T ⟶ S) (h : j ≫ f = a) :
    fibreChart j a f g h ≫ pullback.fst f g = pullback.fst a g ≫ j := by
  subst a
  simp [fibreChart]

@[reassoc] lemma fibreChart_snd {A Y S T : Scheme.{u}} (j : A ⟶ Y) (a : A ⟶ S)
    (f : Y ⟶ S) (g : T ⟶ S) (h : j ≫ f = a) :
    fibreChart j a f g h ≫ pullback.snd f g = pullback.snd a g := by
  subst a
  simp [fibreChart]

instance fibreChart_isOpenImmersion {A Y S T : Scheme.{u}} (j : A ⟶ Y) (a : A ⟶ S)
    (f : Y ⟶ S) (g : T ⟶ S) (h : j ≫ f = a) [IsOpenImmersion j] :
    IsOpenImmersion (fibreChart j a f g h) := by
  dsimp [fibreChart]; infer_instance

lemma fibreChart_range {A Y S T : Scheme.{u}} (j : A ⟶ Y) (a : A ⟶ S)
    (f : Y ⟶ S) (g : T ⟶ S) (h : j ≫ f = a) [IsOpenImmersion j] :
    Set.range (fibreChart j a f g h) = pullback.fst f g ⁻¹' Set.range j := by
  have h₁ := (pullback.congrHom h (rfl : g = g)).inv.surjective
  have h₂ := (pullbackRightPullbackFstIso f g j).inv.surjective
  simp only [fibreChart, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr h₁, Set.image_univ, Set.range_eq_univ.mpr h₂]
  exact IsOpenImmersion.range_pullbackSnd j (pullback.fst f g)

lemma fibreChart_square {A Y S T : Scheme.{u}} (j : A ⟶ Y) (a : A ⟶ S)
    (f : Y ⟶ S) (g : T ⟶ S) (h : j ≫ f = a) :
    IsPullback (pullback.fst a g) (fibreChart j a f g h) j (pullback.fst f g) := by
  have H : IsPullback (pullback.fst a g) (fibreChart j a f g h ≫ pullback.snd f g)
      (j ≫ f) g := by
    simpa only [fibreChart_snd, h] using IsPullback.of_hasPullback a g
  exact H.of_bot (fibreChart_fst j a f g h).symm (IsPullback.of_hasPullback f g)

-- Retain the two-open-chart interface, including the second original open immersion.
@[nolint unusedArguments]
lemma fibreChart_preimage_range {A B Y S T : Scheme.{u}}
    (i : A ⟶ Y) (j : B ⟶ Y) (a : A ⟶ S) (b : B ⟶ S) (f : Y ⟶ S) (g : T ⟶ S)
    (hi : i ≫ f = a) (hj : j ≫ f = b) [IsOpenImmersion i] [IsOpenImmersion j] :
    fibreChart j b f g hj ⁻¹' Set.range (fibreChart i a f g hi) =
      pullback.fst b g ⁻¹' (j ⁻¹' Set.range i) := by
  rw [fibreChart_range]
  ext z
  change pullback.fst f g (fibreChart j b f g hj z) ∈ Set.range i ↔ _
  rw [← Scheme.Hom.comp_apply, fibreChart_fst, Scheme.Hom.comp_apply]
  rfl

end AlgebraicGeometry.Scheme.Pullback.Fibre
