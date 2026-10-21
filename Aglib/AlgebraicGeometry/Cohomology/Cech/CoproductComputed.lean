/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.CoproductComplex
public import Aglib.Algebra.DirectSumTransport

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

/-- Direct sums commute with original cohomology on a finite affine cover,
with the original structural-ring module structures. -/
def moduleCohomologyCoproductLinearEquiv [DecidableEq δ] (q : ℕ) :
    letI : ∀ i, Module R (Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) :=
      fun i => moduleCohomologyModuleOfHom X α (M i) q
    letI := moduleCohomologyModuleOfHom X α (∐ M) q
    (⨁ i, Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) ≃ₗ[R]
      Sheaf.H.{max u v + 1} (moduleAddSheaf X (∐ M)) q := by
  classical
  letI : ∀ i, Module R (Sheaf.H.{max u v + 1} (moduleAddSheaf X (M i)) q) :=
    fun i => moduleCohomologyModuleOfHom X α (M i) q
  letI := moduleCohomologyModuleOfHom X α (∐ M) q
  letI := Scheme.Modules.QuasiCoherent.quasicoherent_coproduct.{u, v} M
  let e (N : X.Modules) [N.IsQuasicoherent] :=
    moduleCechCohomologyLinearEquivAll X α U N hcover (moduleCechIsAffineOpenIntersection X U hU)
      (injectiveResolution (moduleAddSheaf X N)) q
  exact DirectSum.transportEquiv (fun i => e (M i))
    (ModuleCat.coproductComplexHomologyLinearEquiv.{u, v, 0}
      (fun i => moduleCechComplex X α (M i) U) q)
    (homologyMapIso (moduleCechCoproductIso.{u, v} X α U hU M) q).toLinearEquiv
    (e (∐ M))

end AlgebraicGeometry.Scheme.Cohomology
