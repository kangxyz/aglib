/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FiniteProductEmbedding
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Projective

/-!
# Original completion for a finite scheme over a projective product

The source's local Noetherianity is derived, not assumed. The constructed
projective embedding is used only to invoke projective effectivity; the forward
functor remains completion along the original finite-product structural map.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (A : Type u) [CommRing A] [IsNoetherianRing A]
  {n : ℕ} (σ : Fin n → Type u)
  (hfinite : ∀ i, Finite (σ i)) (hnonempty : ∀ i, Nonempty (σ i))
  {Y : Scheme.{u}}
  (q : Y ⟶ (finiteProductOver (fun i => Over.mk (toSpec A (σ i)))).left) [IsFinite q]

include σ hfinite hnonempty q in
/-- Local Noetherianity is a consequence of the constructed projective embedding. -/
theorem isLocallyNoetherian_of_finite_projectiveProduct : IsLocallyNoetherian Y := by
  obtain ⟨m, j, hj, _⟩ :=
    FiniteEmbedding.exists_closedImmersion_of_finite_projectiveProduct σ hfinite hnonempty q
  have : IsClosedImmersion j := hj
  exact LocallyOfFiniteType.isLocallyNoetherian j

/-- Coherent effectivity for the original finite-product structure map over
an arbitrary complete Noetherian base, without flatness or locality assumptions. -/
theorem finiteProjectiveProductCompletionIsEquivalence (I : Ideal A) [IsAdicComplete I A] :
    letI : IsLocallyNoetherian Y :=
      isLocallyNoetherian_of_finite_projectiveProduct A σ hfinite hnonempty q
    (completionFunctor Y (idealThickeningIdealSheaf
      (q ≫ (finiteProductOver (fun i => Over.mk (toSpec A (σ i)))).hom) I)).IsEquivalence := by
  let : IsLocallyNoetherian Y :=
    isLocallyNoetherian_of_finite_projectiveProduct A σ hfinite hnonempty q
  obtain ⟨m, j, hj, hjbase⟩ :=
    FiniteEmbedding.exists_closedImmersion_of_finite_projectiveProduct σ hfinite hnonempty q
  have : IsClosedImmersion j := hj
  have he := projectiveCompletionIsEquivalence A I m j
  rw [hjbase] at he
  exact he

end AlgebraicGeometry.Scheme.Cohomology
