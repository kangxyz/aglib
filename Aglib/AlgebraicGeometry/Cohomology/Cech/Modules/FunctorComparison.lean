/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Modules.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor

/-!
# The native Cech comparison in the original cohomology functor presentation

The adapter changes only the presentation of the target module. Its native
coefficient naturality is established before any coproduct is substituted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CategoryTheory.Cech
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
  {ι : Type u} (U : ι → X.Opens)
  (hcover : iSup U = ⊤)
  (haff : ∀ (p : ℕ) (a : Fin (p + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)))

/-- The original comparison, with the original cohomology functor's module presentation. -/
def moduleCechCohomologyFunctorEquiv (N : X.Modules) [N.IsQuasicoherent]
    (I : InjectiveResolution (moduleAddSheaf X N)) (q : ℕ) :
    (moduleCechComplex X α N U).homology q ≃ₗ[R]
      (moduleCohomologyFunctorOfHom X α q).obj N :=
  moduleCechCohomologyLinearEquivAll X α U N hcover haff I q

/-- Native coefficient naturality with both comparisons in the same functor presentation. -/
theorem moduleCechCohomologyFunctorEquiv_naturality
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (I : InjectiveResolution (moduleAddSheaf X M))
    (J : InjectiveResolution (moduleAddSheaf X N)) (φ : M ⟶ N) (q : ℕ)
    (x : (moduleCechComplex X α M U).homology q) :
    moduleCechCohomologyFunctorEquiv X α U hcover haff N J q
        (homologyMap (moduleCechMap X α U φ) q x) =
      (moduleCohomologyFunctorOfHom X α q).map φ
        (moduleCechCohomologyFunctorEquiv X α U hcover haff M I q x) :=
  moduleCechCohomologyLinearEquivAll_naturality X α U hcover haff I J φ q x

end AlgebraicGeometry.Scheme.Cohomology
