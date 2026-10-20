/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Factorization of reduced schemes into closed subschemes

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.ReducedFactor`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `e1d794a32dee7f82c3a901294c047cf507b85097657bc359339d0476de87b22e`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v

namespace AlgebraicGeometry
variable {Z X : Scheme.{u}} [IsReduced Z]

/-- For a reduced source, support containment really yields the kernel
inequality needed for scheme-theoretic factorization. -/
lemma ideal_le_ker_of_range_subset_support (I : X.IdealSheafData) (f : Z ⟶ X)
    (hf : Set.range f ⊆ I.support) : I ≤ f.ker := by
  have H : (I.comap f).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap]
    ext z
    exact iff_true_intro (hf ⟨z, rfl⟩)
  have H' : I.comap f = ⊥ :=
    Scheme.IdealSheafData.support_eq_top_iff.mp H
  rw [← Scheme.IdealSheafData.map_bot f,
    Scheme.IdealSheafData.le_map_iff_comap_le, H']

/-- A canonical map into an actual closed subscheme, obtained from the
proved kernel inequality rather than equating schemes by their supports. -/
def liftReducedToClosed {C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]
    (f : Z ⟶ X) (hf : Set.range f ⊆ Set.range i) : Z ⟶ C :=
  IsClosedImmersion.lift i f (ideal_le_ker_of_range_subset_support i.ker f
    (by simpa only [Scheme.Hom.support_ker,
      i.isClosedEmbedding.isClosed_range.closure_eq] using hf))

@[reassoc (attr := simp)] lemma liftReducedToClosed_fac {C : Scheme.{u}}
    (i : C ⟶ X) [IsClosedImmersion i] (f : Z ⟶ X)
    (hf : Set.range f ⊆ Set.range i) : liftReducedToClosed i f hf ≫ i = f :=
  IsClosedImmersion.lift_fac ..

end AlgebraicGeometry
