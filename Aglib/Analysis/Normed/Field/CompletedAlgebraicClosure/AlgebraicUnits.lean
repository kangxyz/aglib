/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Analysis.Normed.Field.CompletedAlgebraicClosure.Galois
public import Aglib.FieldTheory.Units.CyclicQuotientDescent

/-!
# The completed action on the actual algebraic unit carrier

Source: `R5Lab.Aglib.Analysis.Normed.Field.CompletedAlgebraicClosure.Galois`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
universe u
namespace AlgebraicClosure.SpectralCompletion
open Units.CyclicQuotient
variable (F : Type u) [NontriviallyNormedField F] [CompleteSpace F]
  [CharZero F] [IsUltrametricDist F]

/-- This is precisely the unit action in the already-verified descent predicate. -/
theorem relativeCompletedAutomorphism_algebraicUnits
    (σ : (algebraicClosure F (Completed F)) ≃ₐ[F] (algebraicClosure F (Completed F)))
    (x : (algebraicClosure F (Completed F))ˣ) :
    Units.map (relativeCompletedAutomorphism F σ).toMonoidHom (algebraicUnits x) =
      algebraicUnits (Units.map σ.toMonoidHom x) := by
  apply Units.ext
  exact relativeCompletedAutomorphism_algebraic F σ x


end AlgebraicClosure.SpectralCompletion
