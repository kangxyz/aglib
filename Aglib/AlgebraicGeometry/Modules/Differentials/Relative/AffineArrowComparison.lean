/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Differentials.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal.Affine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineCoefficientValues
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction


/-!
# Original affine differential coefficient in scalar-adjunction coordinates

The original geometric coefficient is compared with the native scalar-extended
Kähler map by the universal property on original differential generators.
The existing diagonal affine provider is imported for its native global
relative-differential generator equation; it is not reimplemented here.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open CommRingCat.KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {Λ A B : CommRingCat.{u}} (α : Λ ⟶ A) (σ : A ⟶ B)

/-- The actual geometric coefficient has precisely the original algebraic
base-change adjoint, including both original affine adjunction units. -/
theorem affineCoefficient_scalarAdjoint :
    let M := CommRingCat.KaehlerDifferential α
    let N := CommRingCat.KaehlerDifferential (α ≫ σ)
    (tilde.adjunction (R := A)).homEquiv M _
      ((relativeDifferentialAffineIso α).inv ≫
        differentialCoefficient (Spec.map α) (Spec.map σ) ≫
        (pushforward (Spec.map σ)).map
          ((relativeDifferentialCongrIso (Spec.map σ ≫ Spec.map α)
            (Spec.map_comp α σ).symm).hom ≫
            (relativeDifferentialAffineIso (α ≫ σ)).hom)) ≫
      (pushforwardGlobalSectionsIso σ).hom.app (tilde N) =
    (ModuleCat.extendRestrictScalarsAdj σ.hom).homEquiv M
      (moduleSpecΓFunctor.obj (tilde N))
      (affineDifferentialLinearMap α σ ≫ (tilde.adjunction (R := B)).unit.app N) := by
  intro M N
  apply ModuleCat.hom_ext
  let := α.hom.toAlgebra
  let T := (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars σ.hom).obj (tilde N)
  let : Module Λ T := Module.compHom _ α.hom
  let : IsScalarTower Λ A T := IsScalarTower.of_compHom _ _ _
  apply Derivation.liftKaehlerDifferential_unique (M := T)
  ext a
  let := σ.hom.toAlgebra
  change (relativeDifferentialAffineIso (α ≫ σ)).hom.val.app (op ⊤)
    ((relativeDifferentialCongrIso (Spec.map σ ≫ Spec.map α)
      (Spec.map_comp α σ).symm).hom.val.app (op ⊤)
      ((differentialCoefficient (Spec.map α) (Spec.map σ)).val.app (op ⊤)
        ((relativeDifferentialAffineIso α).inv.val.app (op ⊤)
          (tilde.toOpen M ⊤ (CommRingCat.KaehlerDifferential.d a))))) =
    tilde.toOpen N ⊤ (affineDifferentialLinearMap α σ
      ((1 : B) ⊗ₜ[A] CommRingCat.KaehlerDifferential.d (f := α) a))
  rw [Diagonal.relativeDifferentialAffineIso_inv_top, affineDifferentialLinearMap_tmul, one_smul]
  exact affineCoefficient_d α σ a

end AlgebraicGeometry.Scheme.Modules.Differentials
