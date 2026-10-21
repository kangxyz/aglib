/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-! # All relation differentials generate the cotangent kernel

The actual relation generators of an algebra presentation span its conormal module.
Applying the native cotangent differential and exact sequence identifies the kernel of
its map to Kähler differentials. Both variable and relation indices may be infinite.
-/

@[expose] public noncomputable section

open TensorProduct

namespace Algebra.Presentation

variable {A B ι σ : Type*} [CommRing A] [CommRing B] [Algebra A B]

set_option backward.isDefEq.respectTransparency false in
/-- All specified relation classes generate the actual conormal module of a presentation. -/
theorem span_relation_cotangent_eq_top (P : Presentation A B ι σ) :
    Submodule.span B (Set.range fun j =>
      Extension.Cotangent.mk (P := P.toExtension)
        ⟨P.relation j, P.relation_mem_ker j⟩) = ⊤ := by
  simpa only [Generators.toExtension] using
    (Extension.Cotangent.span_eq_top_of_span_eq_ker
      (P := P.toExtension) P.relation P.span_range_relation_eq_ker)

set_option backward.isDefEq.respectTransparency false in
/-- The differentials of all relation generators span exactly the kernel of the actual
map from the relative polynomial cotangent space to Kähler differentials. -/
theorem span_relation_differentials_eq_ker_toKaehler (P : Presentation A B ι σ) :
    Submodule.span B (Set.range fun j =>
      (1 : B) ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring (P.relation j)) =
        LinearMap.ker P.toExtension.toKaehler := by
  have h := congrArg (Submodule.map P.toExtension.cotangentComplex)
    (P.span_relation_cotangent_eq_top)
  rw [Submodule.map_span, Submodule.map_top, ← Set.range_comp'] at h
  simp only [Extension.cotangentComplex_mk] at h
  rw [← LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler] at h
  simpa only [Generators.toExtension, Extension.CotangentSpace] using h


end Algebra.Presentation
