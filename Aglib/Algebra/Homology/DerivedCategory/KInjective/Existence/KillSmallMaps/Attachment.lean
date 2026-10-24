/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.MappingCone.Identity

/-!
# Attaching identity cones to a small family of maps

The attachment is the native pushout of the coproduct evaluation map and the
inclusion into its identity cone. Its original inclusion is monic, and every
original map in the indexed family has a specified nullhomotopy after attachment.
Acyclicity and a quasi-isomorphism claim are deliberately separate: arbitrary
families can be killed this way, but do not preserve homology.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} (A : ι → CochainComplex C ℤ) [HasCoproduct A]
  {K : CochainComplex C ℤ} (f : ∀ i, A i ⟶ K)

/-- Attach the identity cone of the coproduct along the original evaluation. -/
def killSmallMapsAttachment : CochainComplex C ℤ :=
  pushout (Sigma.desc f) (mappingCone.inr (𝟙 (∐ A)))

/-- The original inclusion into the attachment, not a replacement axiom. -/
def killSmallMapsι : K ⟶ killSmallMapsAttachment A f :=
  pushout.inl _ _

/-- The cone map witnessing the attachments. -/
def killSmallMapsConeMap : mappingCone (𝟙 (∐ A)) ⟶ killSmallMapsAttachment A f :=
  pushout.inr _ _

@[reassoc]
lemma killSmallMaps_condition :
    Sigma.desc f ≫ killSmallMapsι A f =
      mappingCone.inr (𝟙 (∐ A)) ≫ killSmallMapsConeMap A f :=
  pushout.condition

set_option backward.isDefEq.respectTransparency false in
instance killSmallMapsι_mono : Mono (killSmallMapsι A f) := by
  have : Mono (mappingCone.inr (𝟙 (∐ A))) := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    exact mono_of_mono_fac (mappingCone.inr_f_snd_v (𝟙 (∐ A)) n)
  exact Abelian.mono_pushout_of_mono_g _ _

set_option backward.isDefEq.respectTransparency false in
/-- The aggregate evaluation becomes nullhomotopic through the actual pushout. -/
def killSmallMapsEvaluationHomotopy :
    Homotopy (Sigma.desc f ≫ killSmallMapsι A f) 0 := by
  have h : Homotopy (mappingCone.inr (𝟙 (∐ A))) 0 := by
    change Homotopy (HomologicalComplex.homotopyCofiber.inr (𝟙 (∐ A))) 0
    simpa only [Category.id_comp] using
      (HomologicalComplex.homotopyCofiber.inrCompHomotopy (𝟙 (∐ A))
        (fun j => ⟨j - 1, by change j - 1 + 1 = j; omega⟩))
  exact (Homotopy.ofEq (killSmallMaps_condition A f)).trans
    ((h.compRight (killSmallMapsConeMap A f)).trans
      (Homotopy.ofEq (by simp)))

/-- Every original map is killed by a specified homotopy, not only in a quotient. -/
def killSmallMapsHomotopy (i : ι) :
    Homotopy (f i ≫ killSmallMapsι A f) 0 := by
  simpa only [← Category.assoc, Sigma.ι_comp_desc, comp_zero] using
    (killSmallMapsEvaluationHomotopy A f).compLeft (Sigma.ι A i)

end CochainComplex
