/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverConstant

/-! # Original sections of trivial finite covers over a one-point scheme

Every section lands in a single coproduct component. The original over-scheme
condition then forces the component map to be the identity, including nilpotents.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable (X : Scheme.{u}) [Nonempty X] [Subsingleton X] (A : Type u) [Finite A]

/-- Actual sections of a trivial finite cover are its literal labels. -/
theorem trivialCoverSection_terminal_bijective :
    Function.Bijective (trivialCoverSection X A (Etale.mk (𝟙 X))) := by
  classical
  let x : X := Classical.choice inferInstance
  refine ⟨fun a b h => trivialCoverSection_label X A _ x a b h, ?_⟩
  intro s
  let q : X ⟶ ∐ fun _ : A => X := s.left ≫ (trivialCoverSigmaIso X A).hom
  obtain ⟨⟨a, z⟩, hz⟩ := (sigmaMk (fun _ : A => X)).surjective (q x)
  have hz' : Sigma.ι (fun _ : A => X) a z = q x := by
    simpa only [sigmaMk_mk] using hz
  have hrange : Set.range q ⊆ Set.range (Sigma.ι (fun _ : A => X) a) := by
    rintro y ⟨t, rfl⟩
    exact ⟨z, hz'.trans (congrArg q (Subsingleton.elim x t))⟩
  let r : X ⟶ X := IsOpenImmersion.lift (Sigma.ι (fun _ : A => X) a) q hrange
  have hfac : r ≫ Sigma.ι (fun _ : A => X) a = q :=
    IsOpenImmersion.lift_fac _ _ _
  have hsection : s.left = r ≫ (trivialCoverι X A a).hom.left := by
    apply (cancel_mono (trivialCoverSigmaIso X A).hom).mp
    rw [Category.assoc, trivialCoverSigmaIso_ι]
    exact hfac.symm
  have hr : r = 𝟙 X := by
    have h := congrArg (fun f => f ≫ (trivialCover X A).obj.hom) hsection
    have h' : r = (Over.mk (Etale.mk (𝟙 X)).hom).hom := by
      simpa only [Category.assoc, trivialCoverι_struct, Category.comp_id, Over.w s] using h.symm
    change r = 𝟙 X at h'
    exact h'
  refine ⟨a, ?_⟩
  apply Over.OverMorphism.ext
  change (𝟙 X) ≫ (trivialCoverι X A a).hom.left = s.left
  rw [hsection, hr]

end AlgebraicGeometry.Scheme.FiniteEtale
