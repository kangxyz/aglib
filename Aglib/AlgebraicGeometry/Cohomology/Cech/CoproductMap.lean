/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Coproduct
public import Aglib.Algebra.Category.ModuleCat.DirectSumMap

/-!
# The original coefficient-induced coproduct map on cohomology
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry DirectSum

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type (max u v)} [CommRing R] (X : Scheme.{max u v}) (α : R →+* Γ(X, ⊤))
  {δ : Type v} (M : δ → X.Modules)

/-- The canonical map from the direct sum, induced by the actual coefficient inclusions. -/
def moduleCohomologyCoproductMap (q : ℕ) :
    let H := moduleCohomologyFunctorOfHom.{max u v} X α q
    (⨁ i, H.obj (M i)) →ₗ[R] H.obj (∐ M) := by
  let H := moduleCohomologyFunctorOfHom.{max u v} X α q
  exact ModuleCat.functorCoproductMap H M

/-- The canonical comparison on a single summand is the original cohomology map. -/
theorem moduleCohomologyCoproductMap_lof [DecidableEq δ] (q : ℕ) (i : δ)
    (x : Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) :
    letI : ∀ i, Module R (Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) :=
      fun i => moduleCohomologyModuleOfHom.{max u v} X α (M i) q
    letI := moduleCohomologyModuleOfHom.{max u v} X α (∐ M) q
    moduleCohomologyCoproductMap.{u, v} X α M q (DirectSum.lof R δ _ i x) =
      moduleCohomologyMapOfHom.{max u v} X α (Sigma.ι M i) q x := by
  let : ∀ i, Module R (Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) :=
    fun i => moduleCohomologyModuleOfHom.{max u v} X α (M i) q
  let := moduleCohomologyModuleOfHom.{max u v} X α (∐ M) q
  let H := moduleCohomologyFunctorOfHom.{max u v} X α q
  exact ModuleCat.functorCoproductMap_lof H M i x

end AlgebraicGeometry.Scheme.Cohomology
