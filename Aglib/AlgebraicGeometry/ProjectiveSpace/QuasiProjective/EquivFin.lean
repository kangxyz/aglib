/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.LinearEmbedding
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-!
# H-quasi-projective schemes with `n + 1` homogeneous coordinates

Let `R` be a commutative ring. An H-quasi-projective `f : X ⟶ Spec R` (`IsHQuasiProjective`)
factors as a quasi-compact immersion into `P(ι)_R = ProjectiveSpace R ι` followed by the structure
morphism, for some finite coordinate type `ι`, which may be empty. Such an immersion can be chosen
with `ι ≃ Fin (n + 1)` for some `n`, that is, into projective space `P^n_R` up to renaming the
coordinates (`AlgebraicGeometry.IsHQuasiProjective.exists_isImmersion_equivFin`): compose the given
immersion `X ⟶ P(ι)_R` with the linear embedding `P(ι)_R ⟶ P(Option ι)_R` of the coordinate
inclusion `some : ι → Option ι` (`ProjectiveSpace.linearEmbedding`), a closed immersion over
`Spec R`, and take `Option ι ≃ Option (Fin (card ι)) ≃ Fin (card ι + 1)`. The composite is again a
quasi-compact immersion over `Spec R`. No hypothesis on `R` is needed.

This puts an H-quasi-projective morphism in the form of Stacks, Definition 29.41.1 (Tag 01VW),
a quasi-compact immersion into `P^n_S` over `S = Spec R`, whose homogeneous coordinates are indexed
by `Fin (n + 1)`. The equivalence is kept as data instead of reindexing to `Fin (n + 1)` itself,
since `Fin (n + 1)` lies in `Type` and `ProjectiveSpace R ι` needs `ι` in the universe of `R`.
Consumer: the quotient by a flat proper equivalence relation,
`Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Existence`, whose Hilbert schemes of an immersed
scheme (`HilbertScheme/Immersed`, `HilbertScheme/Coproduct`) take coordinates `ι ≃ Fin (n + 1)`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} {X : Scheme.{u}}

/-- **H-quasi-projective with `n + 1` coordinates**: an H-quasi-projective `f : X ⟶ Spec R`
factors as a quasi-compact immersion `i : X ⟶ P(ι)_R` followed by the structure morphism, for a
coordinate type `ι ≃ Fin (n + 1)`. The immersion given by `IsHQuasiProjective` is composed with the
linear embedding `P(ι)_R ⟶ P(Option ι)_R`, which also covers an empty coordinate type. -/
theorem IsHQuasiProjective.exists_isImmersion_equivFin (f : X ⟶ Spec R) [IsHQuasiProjective f] :
    ∃ (ι : Type u) (n : ℕ) (_ : ι ≃ Fin (n + 1)) (i : X ⟶ ProjectiveSpace R ι),
      IsImmersion i ∧ QuasiCompact i ∧ i ≫ ProjectiveSpace.toSpec R ι = f := by
  obtain ⟨ι, _, i, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := f)
  exact ⟨Option ι, Nat.card ι,
    (Equiv.optionCongr (Finite.equivFin ι)).trans (finSuccEquiv (Nat.card ι)).symm,
    i ≫ ProjectiveSpace.linearEmbedding R (Option.some_injective ι), inferInstance, inferInstance,
    by rw [Category.assoc, ProjectiveSpace.linearEmbedding_toSpec]⟩

end AlgebraicGeometry
