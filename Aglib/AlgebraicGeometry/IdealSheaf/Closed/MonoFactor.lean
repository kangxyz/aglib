/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Kernel pullback for a closed immersion through a monomorphism

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.MonoFactor`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `f82aee40ae8c3ad7d027abe517b140bd75ee5ebf8b1370ae3cb1449dbe09bf6c`.
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

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A closed immersion factoring through a monomorphism pulls back to its
actual factor, including the full ideal-sheaf structure. -/
lemma ker_comap_of_mono {P U X : Scheme.{u}} (p : P ⟶ U) (i : U ⟶ X)
    [Mono i] [IsClosedImmersion (p ≫ i)] :
    (p ≫ i).ker.comap i = p.ker := by
  have H : IsPullback p (𝟙 P) i (p ≫ i) :=
    (IsPullback.of_horiz_isIso_mono
      (show CommSq (𝟙 P) p (p ≫ i) i from ⟨by simp⟩)).flip
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

end AlgebraicGeometry.Scheme.IdealSheafData
