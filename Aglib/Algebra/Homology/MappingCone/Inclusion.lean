/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.MappingCone.WeakMap

/-!
# Quasi-isomorphism of the original cone inclusion

The native inclusion into the mapping cone of a map from an acyclic complex
is a quasi-isomorphism. The proof uses the original rotated cone short exact
sequence and the native shift comparison on homology, with no boundedness
hypothesis or replacement of the complex carriers.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A K : CochainComplex C ℤ}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original cone inclusion is a quasi-isomorphism when the source of
its defining map is acyclic. No bound on either complex is required. -/
theorem quasiIso_inr_of_acyclic (f : A ⟶ K) (hA : A.Acyclic) :
    QuasiIso (inr f) := by
  have hS := mappingCone_triangle_shortExact f
  have hz (n : ℤ) : IsZero ((A⟦(1 : ℤ)⟧).homology n) :=
    (hA (n + 1)).isZero_homology.of_iso
      ((CochainComplex.ShiftSequence.shiftIso C 1 n (n + 1) (by omega)).app A)
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (homologyMap (inr f) n) :=
    (hS.homology_exact₁ (n - 1) n (by simp)).mono_g ((hz (n - 1)).eq_of_src _ _)
  have he : Epi (homologyMap (inr f) n) :=
    (hS.homology_exact₂ n).epi_f ((hz n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end CochainComplex.mappingCone
