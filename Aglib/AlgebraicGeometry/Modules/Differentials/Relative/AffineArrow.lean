/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Differentials.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / AffineArrow

Source: `IntegralTrace/AffineDifferentialArrow.lean`.
Incoming SHA256: `8daf9e33570b16efa9957574da7ee494b42a3b082bf7325496b0778840cb9c01`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite TensorProduct
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open CommRingCat.KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {Λ A B : CommRingCat.{u}} (α : Λ ⟶ A) (σ : A ⟶ B)

/-- The algebraic arrow transported by the original target affine comparison. -/
def affineDifferentialSheafMap :
    tilde ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)) ⟶
      relativeDifferentialSheaf (Spec.map (α ≫ σ)) :=
  (tilde.functor B).map (affineDifferentialLinearMap α σ) ≫
    (relativeDifferentialAffineIso (α ≫ σ)).inv
set_option backward.isDefEq.respectTransparency false in
/-- Literal differential values on every principal open of the original target. -/
theorem affineDifferentialSheafMap_d (r : B) (a : A) :
    letI := σ.hom.toAlgebra
    (affineDifferentialSheafMap α σ).val.app (op (PrimeSpectrum.basicOpen r))
      (tilde.toOpen ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        (PrimeSpectrum.basicOpen r)
        ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) a)) =
    (relativeDifferentialDerivation (Spec.map (α ≫ σ))).d
      (algebraMap B Γ(Spec B, PrimeSpectrum.basicOpen r) (σ a)) := by
  let := σ.hom.toAlgebra
  change (relativeDifferentialAffineIso (α ≫ σ)).inv.val.app _
    (((tilde.functor B).map (affineDifferentialLinearMap α σ)).val.app _ _) = _
  have h := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (affineDifferentialLinearMap α σ) (PrimeSpectrum.basicOpen r))
    ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) a)
  refine (congrArg ((relativeDifferentialAffineIso (α ≫ σ)).inv.val.app _) h).trans ?_
  have hd := affineDifferentialLinearMap_tmul α σ 1 a
  simp only [one_smul] at hd
  exact (congrArg (fun z => (relativeDifferentialAffineIso (α ≫ σ)).inv.val.app _
    (tilde.toOpen (CommRingCat.KaehlerDifferential (α ≫ σ))
      (PrimeSpectrum.basicOpen r) z)) hd).trans
        (relativeDifferentialAffineIso_inv_d (α ≫ σ) r (σ a))

end AlgebraicGeometry.Scheme.Modules.Differentials
