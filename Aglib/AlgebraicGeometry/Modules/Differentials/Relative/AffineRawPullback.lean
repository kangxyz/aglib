/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Differentials.ExteriorBaseChange
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineRawCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.BaseForms
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient


/-!
# The original raw affine pullback arrow

The raw geometric exterior coefficient and its pullback adjoint agree with
the native scalar-extended raw map through the original affine comparisons
and original adjunction units. This is before any bidual or determinant step.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct
open AlgebraicGeometry.Scheme.Modules

universe u


open CommRingCat.KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {Λ A B : CommRingCat.{u}} (α : Λ ⟶ A) (σ : A ⟶ B) (n : ℕ)

/-- The original raw coefficient in the original scalar-adjunction coordinates. -/
theorem affineRawCoefficient_scalarAdjoint :
    let M := ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential α))
    let N := ModuleCat.of B (⋀[B]^n (CommRingCat.KaehlerDifferential (α ≫ σ)))
    (tilde.adjunction (R := A)).homEquiv M _
      ((baseRawFormsIso α n).inv ≫ rawFormsCoefficient (Spec.map α) (Spec.map σ) n ≫
        (pushforward (Spec.map σ)).map (targetRawFormsAffineIso α σ n).hom) ≫
      (pushforwardGlobalSectionsIso σ).hom.app (tilde N) =
    (ModuleCat.extendRestrictScalarsAdj σ.hom).homEquiv M
      (moduleSpecΓFunctor.obj (tilde N))
      (affineRawLinearMap α σ n ≫ (tilde.adjunction (R := B)).unit.app N) := by
  intro M N
  apply ModuleCat.hom_ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  let := σ.hom.toAlgebra
  change (targetRawFormsAffineIso α σ n).hom.val.app (op ⊤)
    ((rawFormsCoefficient (Spec.map α) (Spec.map σ) n).val.app (op ⊤)
      ((baseRawFormsIso α n).inv.val.app (op ⊤)
        (tilde.toOpen M ⊤ (exteriorPower.ιMulti A n v)))) =
    tilde.toOpen N ⊤ (affineRawLinearMap α σ n
      ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A n v))
  have h := affineRawLinearMap_tmul_mk α σ n 1 v
  simp only [one_smul] at h
  exact (affineRawCoefficient_wedge α σ n v).trans
    (congrArg (tilde.toOpen N ⊤) h.symm)

/-- The actual raw geometric pullback arrow is the native raw base-change map
under the original comparisons, with no determinant-pullback assumption. -/
theorem rawFormsPullback_affine :
    rawFormsPullback (Spec.map α) (Spec.map σ) n ≫
      (targetRawFormsAffineIso α σ n).hom =
    (pullback (Spec.map σ)).map (baseRawFormsIso α n).hom ≫
      (((tildePullbackIso σ).app
        (ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential α)))).hom ≫
        (tilde.functor B).map (affineRawLinearMap α σ n)) := by
  let adj := pullbackPushforwardAdjunction (Spec.map σ)
  let M := ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential α))
  let N := ModuleCat.of B (⋀[B]^n (CommRingCat.KaehlerDifferential (α ≫ σ)))
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, rawFormsPullback_adjoint]
  let k := ((tildePullbackIso σ).app M).hom ≫
    (tilde.functor B).map (affineRawLinearMap α σ n)
  refine Eq.trans ?_ (adj.homEquiv_naturality_left (baseRawFormsIso α n).hom k).symm
  apply (cancel_epi (baseRawFormsIso α n).inv).mp
  refine Eq.trans ?_ ((baseRawFormsIso α n).inv_hom_id_assoc (adj.homEquiv _ _ k)).symm
  apply ((tilde.adjunction (R := A)).homEquiv _ _).injective
  apply (cancel_mono ((pushforwardGlobalSectionsIso σ).hom.app (tilde N))).mp
  have ht : (tilde.adjunction (R := B)).homEquiv _ _
      ((tilde.functor B).map (affineRawLinearMap α σ n)) =
      affineRawLinearMap α σ n ≫ (tilde.adjunction (R := B)).unit.app N := by
    rw [Adjunction.homEquiv_unit]
    exact ((tilde.adjunction (R := B)).unit.naturality (affineRawLinearMap α σ n)).symm
  exact (affineRawCoefficient_scalarAdjoint α σ n).trans
    ((tildePullbackIso_homEquiv σ M (tilde N)
      ((tilde.functor B).map (affineRawLinearMap α σ n))).trans
        (congrArg ((ModuleCat.extendRestrictScalarsAdj σ.hom).homEquiv _ _) ht)).symm

end AlgebraicGeometry.Scheme.Modules.Differentials
