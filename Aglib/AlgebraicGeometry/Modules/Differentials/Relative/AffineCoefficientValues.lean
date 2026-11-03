/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Coefficient


/-!
# The geometric affine coefficient on original global generators

These are values of the original geometric coefficient, not a transported
replacement arrow. The ring-map composition and affine target comparison
retain the same original coefficient ring and original spectrum maps.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {Λ A B : CommRingCat.{u}} (α : Λ ⟶ A) (σ : A ⟶ B)

/-- Original global section pullback sends the original affine scalar to its
literal image, with no chosen field or affine presentation. -/
theorem specMap_appTop_scalar (a : A) :
    (Spec.map σ).appTop ((Scheme.ΓSpecIso A).inv a) =
      (Scheme.ΓSpecIso B).inv (σ a) :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality σ).symm a

/-- The original geometric coefficient, followed by the original structure-map
congruence and affine comparison, preserves the literal ring differential. -/
theorem affineCoefficient_d (a : A) :
    (relativeDifferentialAffineIso (α ≫ σ)).hom.val.app (op ⊤)
      ((relativeDifferentialCongrIso (Spec.map σ ≫ Spec.map α)
        (Spec.map_comp α σ).symm).hom.val.app (op ⊤)
        ((differentialCoefficient (Spec.map α) (Spec.map σ)).val.app (op ⊤)
          ((relativeDifferentialDerivation (Spec.map α)).d
            ((Scheme.ΓSpecIso A).inv a)))) =
    tilde.toOpen (CommRingCat.KaehlerDifferential (α ≫ σ)) ⊤
      (CommRingCat.KaehlerDifferential.d (σ a)) := by
  have hd := differentialCoefficient_d (Spec.map α) (Spec.map σ) ⊤
    ((Scheme.ΓSpecIso A).inv a)
  have hc := relativeDifferentialCongrIso_hom_d (Spec.map σ ≫ Spec.map α)
    (Spec.map_comp α σ).symm (op ⊤)
    ((Spec.map σ).appTop ((Scheme.ΓSpecIso A).inv a))
  have ha := relativeDifferentialAffineIso_hom_d (α ≫ σ) 1 (σ a)
  rw [PrimeSpectrum.basicOpen_one] at ha
  refine (congrArg (fun z => (relativeDifferentialAffineIso (α ≫ σ)).hom.val.app (op ⊤)
    ((relativeDifferentialCongrIso (Spec.map σ ≫ Spec.map α)
      (Spec.map_comp α σ).symm).hom.val.app (op ⊤) z)) hd).trans ?_
  refine (congrArg ((relativeDifferentialAffineIso (α ≫ σ)).hom.val.app (op ⊤)) hc).trans ?_
  exact (congrArg (fun z => (relativeDifferentialAffineIso (α ≫ σ)).hom.val.app (op ⊤)
    ((relativeDifferentialDerivation (Spec.map (α ≫ σ))).d z))
      (specMap_appTop_scalar σ a)).trans ha

end AlgebraicGeometry.Scheme.Modules.Differentials
