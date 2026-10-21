/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.Algebra.Category.ModuleCat.NatTower

/-!
# Compatible cohomology lifts in towers

Vanishing of the next cohomology of every adjacent kernel gives compatible
lifts in the original cohomology tower, at any prescribed stage. A finite
locally free tensor coefficient preserves the actual kernel short exact
sequences. These are conditional lifting lemmas, not a uniform Serre bound:
the geometric associated-graded argument must supply that bound separately.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
  (α : R →+* Γ(X, ⊤))

/-- The actual cohomology map of a short exact sequence is surjective when
the next cohomology of its first term vanishes. -/
theorem moduleCohomologyMap_surjective_of_subsingleton
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (q : ℕ)
    (hK : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) (q + 1))) :
    Function.Surjective (moduleCohomologyMapOfHom X α S.g q) := by
  let := hK
  let := moduleCohomologyModuleOfHom X α S.X₂ q
  let := moduleCohomologyModuleOfHom X α S.X₃ q
  let := moduleCohomologyModuleOfHom X α S.X₁ (q + 1)
  exact (LinearMap.surjective_iff_eq_zero_of_exact
    (moduleCohomologyConnectingOfHom_exact_left X α S hS q)).mpr
      (Subsingleton.elim _ _)

/-- A finite locally free twist preserves the actual short exact kernel
sequence, so vanishing of its next kernel cohomology makes the original
cohomology map surjective. No flatness is required of either endpoint. -/
theorem moduleCohomologyTensorMap_surjective_of_subsingleton
    (L : X.Modules) [IsFiniteLocallyFree X L]
    {M N : X.Modules} (π : M ⟶ N) [Epi π] (q : ℕ)
    (hK : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X
      ((moduleTensorLeftFunctor X L).obj (kernel π))) (q + 1))) :
    Function.Surjective (moduleCohomologyMapOfHom X α
      ((moduleTensorLeftFunctor X L).map π) q) := by
  let S := (ShortComplex.kernelSequence π).map (moduleTensorLeftFunctor X L)
  have hS : S.ShortExact := tensor_shortExact_finiteLocallyFree L
    (ShortComplex.kernelSequence π)
    { exact := ShortComplex.kernelSequence_exact π, epi_g := inferInstanceAs (Epi π) }
  exact moduleCohomologyMap_surjective_of_subsingleton X α S hS q hK

/-- Every element at every level lifts to the native compatible sections of
the original twisted cohomology tower, once one has vanishing for all the
adjacent twisted kernels. This retains the original transition maps. -/
theorem twistedCohomologySectionsEval_surjective
    (F : ℕᵒᵖ ⥤ X.Modules) (L : X.Modules) [IsFiniteLocallyFree X L]
    (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) (q : ℕ)
    (hK : ∀ n, Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X
      ((moduleTensorLeftFunctor X L).obj
        (kernel (F.map (homOfLE (Nat.le_succ n)).op)))) (q + 1)))
    (n : ℕ) :
    Function.Surjective (ModuleCat.sectionsEval
      (F ⋙ moduleTensorLeftFunctor X L ⋙ moduleCohomologyFunctorOfHom X α q) n) := by
  apply ModuleCat.sectionsEval_surjective
  intro k
  let := hF k
  exact moduleCohomologyTensorMap_surjective_of_subsingleton X α L
    (F.map (homOfLE (Nat.le_succ k)).op) q (hK k)

end AlgebraicGeometry.Scheme.Cohomology
