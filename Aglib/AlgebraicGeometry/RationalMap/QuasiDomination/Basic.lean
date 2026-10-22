/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Closed graphs of partial maps

Restricting a global map to the inverse image of an open in a separated target gives
an actual closed graph over the original source. A dense-open map with closed graph
into a proper target extends to the whole source. Scheme-theoretic density, rather
than topological density, propagates a factorization through a closed target.
All constructions allow nonreduced schemes and use the native pullbacks and kernels.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

section RestrictTarget

variable {B P S : Scheme.{u}} (f : B ⟶ P) (p : P ⟶ S) (O : P.Opens)

/-- The base triangle for the restriction to the inverse image of a target open. -/
lemma restrictTarget_comp :
    (f ⁻¹ᵁ O).ι ≫ (f ≫ p) = (f ∣_ O) ≫ (O.ι ≫ p) := by
  simp only [← Category.assoc, morphismRestrict_ι]

/-- The literal graph in the product of the original source and the target open. -/
def restrictTargetGraph : (f ⁻¹ᵁ O).toScheme ⟶ pullback (f ≫ p) (O.ι ≫ p) :=
  pullback.lift (f ⁻¹ᵁ O).ι (f ∣_ O) (restrictTarget_comp f p O)

@[reassoc (attr := simp)]
lemma restrictTargetGraph_fst :
    restrictTargetGraph f p O ≫ pullback.fst (f ≫ p) (O.ι ≫ p) = (f ⁻¹ᵁ O).ι := by
  simp [restrictTargetGraph]

@[reassoc (attr := simp)]
lemma restrictTargetGraph_snd :
    restrictTargetGraph f p O ≫ pullback.snd (f ≫ p) (O.ι ≫ p) = f ∣_ O := by
  simp [restrictTargetGraph]

/-- The restricted graph is the actual base change of the original global graph. -/
lemma isPullback_restrictTargetGraph :
    IsPullback (restrictTargetGraph f p O) (f ⁻¹ᵁ O).ι
      (pullback.map (f ≫ p) (O.ι ≫ p) (f ≫ p) p
        (𝟙 B) O.ι (𝟙 S) (by simp) (by simp))
      (pullback.lift (𝟙 B) f (Category.id_comp (f ≫ p))) := by
  let q := pullback.map (f ≫ p) (O.ι ≫ p) (f ≫ p) p
    (𝟙 B) O.ι (𝟙 S) (by simp) (by simp)
  let γ := pullback.lift (𝟙 B) f (Category.id_comp (f ≫ p))
  have hw : restrictTargetGraph f p O ≫ q = (f ⁻¹ᵁ O).ι ≫ γ := by
    apply pullback.hom_ext <;> simp [q, γ, restrictTargetGraph]
  apply IsPullback.of_isLimit (c := PullbackCone.mk (restrictTargetGraph f p O)
    (f ⁻¹ᵁ O).ι hw)
  let H := isPullback_morphismRestrict f O
  refine PullbackCone.IsLimit.mk _
    (fun s => H.lift (s.fst ≫ pullback.snd (f ≫ p) (O.ι ≫ p)) s.snd (by
      have h := congrArg (fun k => k ≫ pullback.snd (f ≫ p) p) s.condition
      simpa [q, γ] using h)) ?_ ?_ ?_
  · intro s
    apply pullback.hom_ext
    · have h := congrArg (fun k => k ≫ pullback.fst (f ≫ p) p) s.condition
      simpa [q, γ] using h.symm
    · simp
  · intro s
    simp
  · intro s m hm₁ hm₂
    apply (cancel_mono (f ⁻¹ᵁ O).ι).mp
    simpa [H] using hm₂

/-- No density hypothesis is needed for the closed-graph construction itself. -/
instance restrictTargetGraph_isClosedImmersion [IsSeparated p] :
    IsClosedImmersion (restrictTargetGraph f p O) :=
  MorphismProperty.of_isPullback (isPullback_restrictTargetGraph f p O).flip inferInstance

end RestrictTarget

section ProperTarget

variable {B Y S : Scheme.{u}} (pB : B ⟶ S) (pY : Y ⟶ S)
  (U : B.Opens) (g : U.toScheme ⟶ Y) (w : U.ι ≫ pB = g ≫ pY)

/-- A closed graph into a proper target makes the domain inclusion proper. -/
lemma isProper_domain_of_closedGraph [IsProper pY]
    [IsClosedImmersion (pullback.lift U.ι g w)] : IsProper U.ι := by
  have : IsProper (pullback.lift U.ι g w ≫ pullback.fst pB pY) := inferInstance
  simpa using this

/-- A dense open with closed graph into a proper target is the entire source. -/
lemma isIso_domain_of_closedGraph [IsProper pY]
    [IsClosedImmersion (pullback.lift U.ι g w)] (hU : Dense (U : Set B)) :
    IsIso U.ι := by
  let : IsProper U.ι := isProper_domain_of_closedGraph pB pY U g w
  let : IsDominant U.ι := Opens.isDominant_ι hU
  exact (isIso_iff_isOpenImmersion_and_surjective U.ι).mpr ⟨inferInstance, inferInstance⟩

/-- The extension uses the inverse of the original domain inclusion. -/
def properExtension [IsProper pY] [IsClosedImmersion (pullback.lift U.ι g w)]
    (hU : Dense (U : Set B)) : B ⟶ Y := by
  letI := isIso_domain_of_closedGraph pB pY U g w hU
  exact inv U.ι ≫ g

@[reassoc (attr := simp)]
lemma domain_properExtension [IsProper pY]
    [IsClosedImmersion (pullback.lift U.ι g w)] (hU : Dense (U : Set B)) :
    U.ι ≫ properExtension pB pY U g w hU = g := by
  let := isIso_domain_of_closedGraph pB pY U g w hU
  simp [properExtension]

@[reassoc (attr := simp)]
lemma properExtension_comp [IsProper pY]
    [IsClosedImmersion (pullback.lift U.ι g w)] (hU : Dense (U : Set B)) :
    properExtension pB pY U g w hU ≫ pY = pB := by
  let := isIso_domain_of_closedGraph pB pY U g w hU
  apply (cancel_epi U.ι).mp
  simpa using w.symm

end ProperTarget

section ClosedTarget

variable {T B Y Z : Scheme.{u}} (j : T ⟶ B) [IsSchemeTheoreticallyDominant j]
  (i : Z ⟶ Y) [IsClosedImmersion i] (f : B ⟶ Y) (g : T ⟶ Z)
  (w : j ≫ f = g ≫ i)

omit [IsClosedImmersion i] in
include j g w in
/-- Schematic density, expressed by the native zero kernel, propagates the
closed-target condition from the given subspace to the original source. -/
lemma closedTarget_kernel_le : i.ker ≤ f.ker := by
  calc
    i.ker ≤ (g ≫ i).ker := g.le_ker_comp i
    _ = (j ≫ f).ker := congrArg Hom.ker w.symm
    _ = f.ker := by rw [Hom.ker_comp, j.ker_eq_bot, IdealSheafData.map_bot]

/-- The original global map factors through the original closed target. -/
def closedTargetLift : B ⟶ Z :=
  IsClosedImmersion.lift i f (closedTarget_kernel_le j i f g w)

@[reassoc (attr := simp)]
lemma closedTargetLift_comp : closedTargetLift j i f g w ≫ i = f :=
  IsClosedImmersion.lift_fac _ _ _

/-- The factorization preserves the literal originally specified map. -/
@[reassoc (attr := simp)]
lemma comp_closedTargetLift : j ≫ closedTargetLift j i f g w = g := by
  apply (cancel_mono i).mp
  simpa using w

/-- The factorization is unique, without any reducedness assumption. -/
lemma closedTargetLift_unique (a : B ⟶ Z) (ha : a ≫ i = f) :
    a = closedTargetLift j i f g w := by
  apply (cancel_mono i).mp
  simpa using ha

end ClosedTarget

/-- A closed subscheme containing a schematically dense map is the whole scheme.
The source and target may both be nonreduced. -/
lemma isIso_closedImmersion_of_dense_factor {T B Z : Scheme.{u}}
    (j : T ⟶ B) [IsSchemeTheoreticallyDominant j]
    (i : Z ⟶ B) [IsClosedImmersion i] (a : T ⟶ Z) (h : a ≫ i = j) :
    IsIso i := by
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply le_bot_iff.mp
  calc
    i.ker ≤ (a ≫ i).ker := a.le_ker_comp i
    _ = j.ker := congrArg Hom.ker h
    _ = ⊥ := j.ker_eq_bot

/-- Equality on a schematically dense source extends into a relatively separated
 target, without requiring the source to be reduced or the dense map to be
 quasi-compact. -/
lemma hom_ext_of_schemeTheoreticallyDominant {T B Y S : Scheme.{u}}
    (j : T ⟶ B) [IsSchemeTheoreticallyDominant j]
    (p : Y ⟶ S) [IsSeparated p] {f g : B ⟶ Y}
    (hbase : f ≫ p = g ≫ p) (h : j ≫ f = j ≫ g) : f = g := by
  let B' : Over S := Over.mk (f ≫ p)
  let Y' : Over S := Over.mk p
  let T' : Over S := Over.mk (j ≫ f ≫ p)
  let f' : B' ⟶ Y' := Over.homMk f
  let g' : B' ⟶ Y' := Over.homMk g hbase.symm
  let j' : T' ⟶ B' := Over.homMk j
  have hj : j' ≫ f' = j' ≫ g' := by
    ext1
    exact h
  let a := (equalizer.lift j' hj).left
  have ha : a ≫ (equalizer.ι f' g').left = j := by
    change (equalizer.lift j' hj).left ≫ (equalizer.ι f' g').left = j'.left
    rw [← Over.comp_left, equalizer.lift_ι]
  let : IsSeparated Y'.hom := ‹IsSeparated p›
  let : IsIso (equalizer.ι f' g').left :=
    isIso_closedImmersion_of_dense_factor j (equalizer.ι f' g').left a ha
  apply (cancel_epi (equalizer.ι f' g').left).mp
  exact congr($(equalizer.condition f' g').left)

end AlgebraicGeometry.Scheme.QuasiDomination
