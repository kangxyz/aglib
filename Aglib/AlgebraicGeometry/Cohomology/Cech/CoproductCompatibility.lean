/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductComputed
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules.FunctorComparison

/-!
# Whole-family compatibility for the finite-affine coproduct computation
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

include hU in
/-- The whole family of native complex inclusions. -/
theorem moduleCechCoproductFamilyInclusions :
    let K := fun i => moduleCechComplex X α (M i) U
    ∀ i, ModuleCat.coproductComplexι.{u, v, 0} K i ≫
      (moduleCechCoproductIso.{u, v} X α U hU M).hom =
        moduleCechMap X α U (Sigma.ι M i) :=
  fun i => moduleCechCoproductIso_ι.{u, v} X α U hU M i

omit [Finite ι] in
include hcover hU in
/-- Native cohomology naturality for the whole family of coefficient inclusions. -/
theorem moduleCechCoproductFamilyNaturality (q : ℕ) :
    let H := moduleCohomologyFunctorOfHom.{max u v} X α q
    letI := Scheme.Modules.QuasiCoherent.quasicoherent_coproduct.{u, v} M
    let e (N : X.Modules) [N.IsQuasicoherent] :
        (moduleCechComplex X α N U).homology q ≃ₗ[R] H.obj N :=
      moduleCechCohomologyFunctorEquiv X α U hcover
        (moduleCechIsAffineOpenIntersection X U hU) N
        (injectiveResolution (moduleAddSheaf X N)) q
    ∀ i y, e (∐ M) (homologyMap (moduleCechMap X α U (Sigma.ι M i)) q y) =
      H.map (Sigma.ι M i) (e (M i) y) := by
  let := Scheme.Modules.QuasiCoherent.quasicoherent_coproduct.{u, v} M
  exact fun i y => moduleCechCohomologyFunctorEquiv_naturality.{max u v}
    X α U hcover (moduleCechIsAffineOpenIntersection X U hU)
    (injectiveResolution (moduleAddSheaf X (M i)))
    (injectiveResolution (moduleAddSheaf X (∐ M))) (Sigma.ι M i) q y

end AlgebraicGeometry.Scheme.Cohomology
