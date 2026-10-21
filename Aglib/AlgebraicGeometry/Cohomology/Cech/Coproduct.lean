/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductComputedInclusions

/-!
# The canonical coproduct comparison on quasi-compact separated schemes
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech DirectSum

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type (max u v)} [CommRing R] (X : Scheme.{max u v}) (α : R →+* Γ(X, ⊤))
  {δ : Type v} (M : δ → X.Modules)

variable [X.IsSeparated] [∀ i, (M i).IsQuasicoherent]

/-- On a quasi-compact separated scheme, the original direct-sum comparison is bijective. -/
theorem moduleCohomologyCoproductMap_bijective [CompactSpace X] (q : ℕ) :
    Function.Bijective (moduleCohomologyCoproductMap.{u, v} X α M q) := by
  classical
  let C := X.affineCover.finiteSubcover
  let V : C.I₀ → X.Opens := fun i => (C.f i).opensRange
  have hV : ∀ i, IsAffineOpen (V i) := fun i => isAffineOpen_opensRange (C.f i)
  have hcoverV : iSup V = ⊤ := C.iSup_opensRange
  exact ModuleCat.FunctorCoproductMapBijective.bijective
    (moduleCohomologyFunctorOfHom.{max u v} X α q) M
    (moduleCohomologyCoproductMap_bijective_of_finiteCover.{u, v}
      X α M V hcoverV hV q)


/-- The canonical cover-independent comparison, with the unchanged forward map,
for quasicoherent families on a quasi-compact separated scheme. -/
def moduleCohomologyCoproductEquiv [CompactSpace X] (q : ℕ) :
    letI : ∀ i, Module R (Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) q
    letI := moduleCohomologyModuleOfHom X α (∐ M) q
    (⨁ i, Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) ≃ₗ[R]
      Sheaf.H.{max u v + 1} (moduleAddSheaf X (∐ M)) q :=
  LinearEquiv.ofBijective (moduleCohomologyCoproductMap.{u, v} X α M q)
    (moduleCohomologyCoproductMap_bijective.{u, v} X α M q)


end AlgebraicGeometry.Scheme.Cohomology
