/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductComplex
public import Aglib.Algebra.Homology.ModuleCat.CoproductEquivalence
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules.FunctorComparison
public import Aglib.AlgebraicGeometry.Cohomology.Modules.FunctorCoproduct

/-!
# The finite-affine computation of coproduct cohomology
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

/-- Every nonempty finite intersection occurring in the Cech complex is affine. -/
theorem moduleCechIsAffineOpenIntersection (X : Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) [X.IsSeparated] (hU : ∀ i, IsAffineOpen (U i))
    (p : ℕ) (a : Fin (p + 1) → ι) :
    IsAffineOpen (∏ᶜ fun k => U (a k)) := by
  have he : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
    apply le_antisymm
    · exact le_iInf fun k => leOfHom (Limits.Pi.π _ k)
    · exact leOfHom (Limits.Pi.lift fun k => homOfLE (iInf_le _ k))
  rw [he]
  exact IsAffineOpen.iInf (fun k => hU (a k))

open scoped Classical in
/-- The finite-affine computation in the original module-valued cohomology functor.
The complex comparisons are assembled before changing the carrier presentation. -/
def moduleCohomologyFunctorCoproductLinearEquiv [DecidableEq δ] (q : ℕ) :
    (⨁ i, (moduleCohomologyFunctorOfHom X α q).obj (M i)) ≃ₗ[R]
      (moduleCohomologyFunctorOfHom X α q).obj (∐ M) :=
  let N : X.Modules := ∐ M
  letI : N.IsQuasicoherent := Scheme.Modules.QuasiCoherent.quasicoherent_coproduct.{u, v} M
  let H := moduleCohomologyFunctorOfHom.{max u v} X α q
  let e (N : X.Modules) [N.IsQuasicoherent] :
      (moduleCechComplex X α N U).homology q ≃ₗ[R] H.obj N :=
    moduleCechCohomologyFunctorEquiv X α U hcover
      (moduleCechIsAffineOpenIntersection X U hU) N
      (injectiveResolution (moduleAddSheaf X N)) q
  let eN : (moduleCechComplex X α N U).homology q ≃ₗ[R] H.obj N := e N
  ModuleCat.coproductEquivOfComplex.{u, v, 0, max u v + 1, max u v + 1}
    (fun i => moduleCechComplex X α (M i) U) (moduleCechComplex X α N U)
    (moduleCechCoproductIso.{u, v} X α U hU M) q
    (V := fun i => H.obj (M i)) (W := H.obj N) (fun i => e (M i)) eN

open scoped Classical in
/-- Direct sums commute with original cohomology on a finite affine cover,
with the original structural-ring module structures. -/
def moduleCohomologyCoproductLinearEquiv [DecidableEq δ] (q : ℕ) :
    letI : ∀ i, Module R (Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) q
    letI := moduleCohomologyModuleOfHom X α (∐ M) q
    (⨁ i, Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) ≃ₗ[R]
      Sheaf.H.{max u v + 1} (moduleAddSheaf X (∐ M)) q := by
  letI : ∀ i, Module R (Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) :=
    fun i => moduleCohomologyModuleOfHom X α (M i) q
  letI := moduleCohomologyModuleOfHom X α (∐ M) q
  letI := Scheme.Modules.QuasiCoherent.quasicoherent_coproduct.{u, v} M
  exact
    ModuleCat.coproductEquivOfComplex.{u, v, 0, _, _}
      (fun i => moduleCechComplex X α (M i) U) (moduleCechComplex X α (∐ M) U)
      (moduleCechCoproductIso.{u, v} X α U hU M) q
      (fun i => moduleCechCohomologyLinearEquivAll X α U (M i) hcover
        (moduleCechIsAffineOpenIntersection X U hU)
        (injectiveResolution (moduleAddSheaf X (M i))) q)
      (moduleCechCohomologyLinearEquivAll X α U (∐ M) hcover
        (moduleCechIsAffineOpenIntersection X U hU)
        (injectiveResolution (moduleAddSheaf X (∐ M))) q)

end AlgebraicGeometry.Scheme.Cohomology
