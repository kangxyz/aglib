/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductMap
public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductCompatibility
public import Aglib.Algebra.Homology.ModuleCat.CoproductTransport

/-!
# Canonical inclusions in the finite-affine coproduct computation
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

variable {ι : Type (max u v)} [Finite ι] (U : ι → X.Opens) [X.IsSeparated]
  (hcover : iSup U = ⊤) (hU : ∀ i, IsAffineOpen (U i))
  [∀ i, (M i).IsQuasicoherent]

include hcover hU in
/-- The actual canonical map is bijective on a finite affine cover. The proof
specializes the abstract transport theorem without re-presenting its composite equality. -/
theorem moduleCohomologyCoproductMap_bijective_of_finiteCover (q : ℕ) :
    ModuleCat.FunctorCoproductMapBijective
      (moduleCohomologyFunctorOfHom.{max u v} X α q) M := by
  classical
  let H := moduleCohomologyFunctorOfHom.{max u v} X α q
  let := Scheme.Modules.QuasiCoherent.quasicoherent_coproduct.{u, v} M
  let K := fun i => moduleCechComplex X α (M i) U
  let e (N : X.Modules) [N.IsQuasicoherent] :
      (moduleCechComplex X α N U).homology q ≃ₗ[R] H.obj N :=
    moduleCechCohomologyFunctorEquiv X α U hcover
      (moduleCechIsAffineOpenIntersection X U hU) N
      (injectiveResolution (moduleAddSheaf X N)) q
  refine ModuleCat.functorCoproductMap_bijective_of_complex.{u, v, 0, _, _, _}
    H M K (moduleCechComplex X α (∐ M) U) ?_ q ?_ ?_ ?_ ?_ ?_
  · exact moduleCechCoproductIso.{u, v} X α U hU M
  · exact fun i => e (M i)
  · exact e (∐ M)
  · exact fun i => moduleCechMap X α U (Sigma.ι M i)
  · exact moduleCechCoproductFamilyInclusions.{u, v} X α M U hU
  · exact moduleCechCoproductFamilyNaturality.{u, v} X α M U hcover hU q

end AlgebraicGeometry.Scheme.Cohomology
