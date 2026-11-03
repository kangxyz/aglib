/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Differentials.BaseChange
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineCoefficientCoordinates
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.BaseForms
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.AffineMaps


/-!
# Original raw affine coefficient values

The comparisons retain the original relative sheaves and structure-map
congruence. Original raw wedges, including the fixed integral basis wedge,
are followed through the actual geometric coefficient map.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TensorProduct
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u


open AlgebraicGeometry.Scheme.Modules
open CommRingCat.KaehlerDifferential

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {Λ A B : CommRingCat.{u}} (α : Λ ⟶ A) (σ : A ⟶ B) (n : ℕ)

/-- Original affine source comparison on each original raw global wedge. -/
theorem baseRawFormsIso_inv_wedge (v : Fin n → CommRingCat.KaehlerDifferential α) :
    (baseRawFormsIso α n).inv.val.app (op ⊤)
      (tilde.toOpen (ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential α))) ⊤
        (exteriorPower.ιMulti A n v)) =
    wedgeAt (Spec A) (relativeDifferentialSheaf (Spec.map α)) n ⊤
      (fun i => (relativeDifferentialAffineIso α).inv.val.app (op ⊤)
        (tilde.toOpen (CommRingCat.KaehlerDifferential α) ⊤ (v i))) := by
  change ((moduleExteriorPowerFunctor (Spec A) n).map
    (relativeDifferentialAffineIso α).inv).val.app (op ⊤)
      ((exteriorTildeIso (CommRingCat.KaehlerDifferential α) n).inv.val.app (op ⊤) _) = _
  refine (congrArg (((moduleExteriorPowerFunctor (Spec A) n).map
    (relativeDifferentialAffineIso α).inv).val.app (op ⊤))
      (exteriorTildeIso_inv_mk_top (CommRingCat.KaehlerDifferential α) n v)).trans ?_
  exact SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk (Spec A).sheaf
    (relativeDifferentialAffineIso α).inv n (op ⊤)
    (fun i => tilde.toOpen (CommRingCat.KaehlerDifferential α) ⊤ (v i))

/-- The original target structure congruence followed by the original affine comparison. -/
def targetRawFormsAffineIso :
    moduleExteriorPower (Spec B)
      (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n ≅
    tilde (ModuleCat.of B (⋀[B]^n (CommRingCat.KaehlerDifferential (α ≫ σ)))) :=
  (moduleExteriorPowerFunctor (Spec B) n).mapIso
    (relativeDifferentialCongrIso (Spec.map σ ≫ Spec.map α) (Spec.map_comp α σ).symm) ≪≫
      baseRawFormsIso (α ≫ σ) n

/-- The original target comparison preserves the actual ordered wedge of sections. -/
theorem targetRawFormsAffineIso_wedge
    (v : Fin n → (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)).val.obj (op ⊤)) :
    (targetRawFormsAffineIso α σ n).hom.val.app (op ⊤)
      (wedgeAt (Spec B) (relativeDifferentialSheaf (Spec.map σ ≫ Spec.map α)) n ⊤ v) =
    (exteriorTildeIso (CommRingCat.KaehlerDifferential (α ≫ σ)) n).hom.val.app (op ⊤)
      (wedgeAt (Spec B) (tilde (CommRingCat.KaehlerDifferential (α ≫ σ))) n ⊤
        (fun i => (relativeDifferentialAffineIso (α ≫ σ)).hom.val.app (op ⊤)
          ((relativeDifferentialCongrIso (Spec.map σ ≫ Spec.map α)
            (Spec.map_comp α σ).symm).hom.val.app (op ⊤) (v i)))) := by
  let c := (relativeDifferentialCongrIso (Spec.map σ ≫ Spec.map α)
    (Spec.map_comp α σ).symm).hom
  let e := (relativeDifferentialAffineIso (α ≫ σ)).hom
  let t := (exteriorTildeIso (CommRingCat.KaehlerDifferential (α ≫ σ)) n).hom
  change t.val.app (op ⊤)
    (((moduleExteriorPowerFunctor (Spec B) n).map e).val.app (op ⊤)
      (((moduleExteriorPowerFunctor (Spec B) n).map c).val.app (op ⊤) _)) = _
  refine (congrArg (fun z => t.val.app (op ⊤)
    (((moduleExteriorPowerFunctor (Spec B) n).map e).val.app (op ⊤) z))
      (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk (Spec B).sheaf
        c n (op ⊤) v)).trans ?_
  exact congrArg (t.val.app (op ⊤))
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk (Spec B).sheaf
      e n (op ⊤) (fun i => c.val.app (op ⊤) (v i)))

/-- The actual raw geometric coefficient retains every original ordered vector. -/
theorem affineRawCoefficient_wedge (v : Fin n → CommRingCat.KaehlerDifferential α) :
    letI := σ.hom.toAlgebra
    (targetRawFormsAffineIso α σ n).hom.val.app (op ⊤)
      ((rawFormsCoefficient (Spec.map α) (Spec.map σ) n).val.app (op ⊤)
        ((baseRawFormsIso α n).inv.val.app (op ⊤)
          (tilde.toOpen (ModuleCat.of A (⋀[A]^n (CommRingCat.KaehlerDifferential α))) ⊤
            (exteriorPower.ιMulti A n v)))) =
    tilde.toOpen (ModuleCat.of B (⋀[B]^n (CommRingCat.KaehlerDifferential (α ≫ σ)))) ⊤
      (exteriorPower.ιMulti B n
        (fun i => affineDifferentialLinearMap α σ ((1 : B) ⊗ₜ[A] v i))) := by
  let := σ.hom.toAlgebra
  let w := fun i => (relativeDifferentialAffineIso α).inv.val.app (op ⊤)
    (tilde.toOpen (CommRingCat.KaehlerDifferential α) ⊤ (v i))
  refine (congrArg (fun z => (targetRawFormsAffineIso α σ n).hom.val.app (op ⊤)
    ((rawFormsCoefficient (Spec.map α) (Spec.map σ) n).val.app (op ⊤) z))
      (baseRawFormsIso_inv_wedge α n v)).trans ?_
  refine (congrArg ((targetRawFormsAffineIso α σ n).hom.val.app (op ⊤))
    (rawFormsCoefficient_wedge (Spec.map α) (Spec.map σ) n ⊤ w)).trans ?_
  refine (targetRawFormsAffineIso_wedge α σ n
    (fun i => (differentialCoefficient (Spec.map α) (Spec.map σ)).val.app (op ⊤)
      (w i))).trans ?_
  have hv := funext (fun i => affineCoefficient_apply α σ (v i))
  refine (congrArg (fun z =>
    (exteriorTildeIso (CommRingCat.KaehlerDifferential (α ≫ σ)) n).hom.val.app (op ⊤)
      (wedgeAt (Spec B) (tilde (CommRingCat.KaehlerDifferential (α ≫ σ))) n ⊤ z)) hv).trans ?_
  exact exteriorTildeIso_hom_mk_top (CommRingCat.KaehlerDifferential (α ≫ σ)) n
    (fun i => affineDifferentialLinearMap α σ ((1 : B) ⊗ₜ[A] v i))

end AlgebraicGeometry.Scheme.Modules.Differentials
