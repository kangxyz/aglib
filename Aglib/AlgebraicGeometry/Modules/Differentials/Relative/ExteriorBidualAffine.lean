/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Affine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorAffine
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FormsFiniteType
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Affine
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Affine


/-!
# AlgebraicGeometry / Modules / Differentials / Relative / ExteriorBidualAffine

Source: `IntegralTrace/AffineForms.lean`.
Incoming SHA256: `ea11236c4f28ac7e3ee837ae044c406f72d7e17b25e0cd53ada761d5e6f8034f`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X : Scheme.{u}} {Λ R : CommRingCat.{u}}
  (a : X ⟶ Spec Λ) (j : Spec R ⟶ X) [IsOpenImmersion j] (n : ℕ)

/-- The actual sheaf bidual sections are the algebraic bidual of the same raw forms. -/
def bidualFormsAffineSectionsEquiv [IsLocallyNoetherian X] [LocallyOfFiniteType a] :
    moduleSpecΓFunctor.obj
      ((show X.Modules from Invertible.dualSheaf X (Invertible.dualSheaf X
        (moduleExteriorPower X (relativeDifferentialSheaf a) n))).restrict j) ≃ₗ[R]
      Module.Dual R (Module.Dual R
        (⋀[R]^n (CommRingCat.KaehlerDifferential (Spec.preimage (j ≫ a))))) := by
  let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
  have hM : affineLocallyFiniteType X M := rawForms_affineLocallyFiniteType a n
  let : (M.restrict j).IsQuasicoherent := (hM R j).1
  let : ((show X.Modules from Invertible.dualSheaf X M).restrict j).IsQuasicoherent :=
    ((affineLocallyFiniteType_dualSheaf M hM) R j).1
  exact (Invertible.affineBidualSectionsEquiv j M).trans
    (rawFormsAffineSectionsEquiv a j n).dualMap.dualMap
private theorem bidualCoordinate_equiv
    {K A B C P : Type*} [CommSemiring K]
    [AddCommMonoid A] [Module K A] [AddCommMonoid B] [Module K B]
    [AddCommMonoid C] [Module K C] [AddCommMonoid P] [Module K P]
    (d0 : B ≃ₗ[K] Module.Dual K A)
    (d1 : C ≃ₗ[K] Module.Dual K B) (e : A ≃ₗ[K] P) :
    (d1.trans (d0.arrowCongr (LinearEquiv.refl K K))).trans e.dualMap.dualMap =
      d1.trans (d0.trans e.symm.dualMap).symm.dualMap := by
  apply LinearEquiv.ext
  intro s
  apply LinearMap.ext
  intro ell
  rfl

private theorem bidualCoordinate_equiv_function
    {K A B C P : Type*} [CommSemiring K]
    [AddCommMonoid A] [Module K A] [AddCommMonoid B] [Module K B]
    [AddCommMonoid C] [Module K C] [AddCommMonoid P] [Module K P]
    (d0 : B ≃ₗ[K] Module.Dual K A)
    (d1 : C ≃ₗ[K] Module.Dual K B) (e : A ≃ₗ[K] P) :
    DFunLike.coe
        ((d1.trans (d0.arrowCongr (LinearEquiv.refl K K))).trans e.dualMap.dualMap) =
      DFunLike.coe (d1.trans (d0.trans e.symm.dualMap).symm.dualMap) :=
  congrArg DFunLike.coe (bidualCoordinate_equiv d0 d1 e)

/-- The original bidual form coordinate is the two original affine dual coordinates. -/
theorem bidualFormsAffineSectionsEquiv_eq_dualCoordinate
    [IsLocallyNoetherian X] [LocallyOfFiniteType a] :
    let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
    let hM : affineLocallyFiniteType X M := rawForms_affineLocallyFiniteType a n
    letI : (M.restrict j).IsQuasicoherent := (hM R j).1
    letI : ((show X.Modules from Invertible.dualSheaf X M).restrict j).IsQuasicoherent :=
      ((affineLocallyFiniteType_dualSheaf M hM) R j).1
    bidualFormsAffineSectionsEquiv a j n =
      (Invertible.affineDualSectionsEquiv j (Invertible.dualSheaf X M)).trans
        ((Invertible.affineDualSectionsEquiv j M).trans
          (rawFormsAffineSectionsEquiv a j n).symm.dualMap).symm.dualMap := by
  let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
  have hM : affineLocallyFiniteType X M := rawForms_affineLocallyFiniteType a n
  let : (M.restrict j).IsQuasicoherent := (hM R j).1
  let : ((show X.Modules from Invertible.dualSheaf X M).restrict j).IsQuasicoherent :=
    ((affineLocallyFiniteType_dualSheaf M hM) R j).1
  exact bidualCoordinate_equiv (Invertible.affineDualSectionsEquiv j M)
    (Invertible.affineDualSectionsEquiv j (Invertible.dualSheaf X M))
    (rawFormsAffineSectionsEquiv a j n)
/-- The complete function of the original bidual coordinate is its two affine dual coordinates. -/
theorem bidualFormsAffineSectionsEquiv_coe_eq_dualCoordinate
    [IsLocallyNoetherian X] [LocallyOfFiniteType a] :
    let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
    let hM : affineLocallyFiniteType X M := rawForms_affineLocallyFiniteType a n
    letI : (M.restrict j).IsQuasicoherent := (hM R j).1
    letI : ((show X.Modules from Invertible.dualSheaf X M).restrict j).IsQuasicoherent :=
      ((affineLocallyFiniteType_dualSheaf M hM) R j).1
    DFunLike.coe (bidualFormsAffineSectionsEquiv a j n) =
      DFunLike.coe
        ((Invertible.affineDualSectionsEquiv j (Invertible.dualSheaf X M)).trans
          ((Invertible.affineDualSectionsEquiv j M).trans
            (rawFormsAffineSectionsEquiv a j n).symm.dualMap).symm.dualMap) := by
  let M := moduleExteriorPower X (relativeDifferentialSheaf a) n
  have hM : affineLocallyFiniteType X M := rawForms_affineLocallyFiniteType a n
  let : (M.restrict j).IsQuasicoherent := (hM R j).1
  let : ((show X.Modules from Invertible.dualSheaf X M).restrict j).IsQuasicoherent :=
    ((affineLocallyFiniteType_dualSheaf M hM) R j).1
  exact bidualCoordinate_equiv_function (Invertible.affineDualSectionsEquiv j M)
    (Invertible.affineDualSectionsEquiv j (Invertible.dualSheaf X M))
    (rawFormsAffineSectionsEquiv a j n)

end AlgebraicGeometry.Scheme.Modules.Differentials
