/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesPresheafComparison
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesLocalAction

/-! # The original homogeneous coefficient square on complete section sheaves -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

open Modules.Rees

variable {A : Type u} [CommRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (F : X.Modules) [F.IsQuasicoherent]

/-- The actual homogeneous inclusion into geometric Rees sections. -/
def reesHomogeneousSections (n : ℕ) :
    moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (reesPowerFamily I f F n) ⟶
    moduleSectionsPresheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (reesPushforwardCoefficient I f F) :=
  (moduleSectionsPresheafFunctor X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).map
      (Sigma.ι (reesPowerFamily I f F) n) ≫ (reesPowerSectionsIso I f F).hom

/-- On the affine basis the global inclusion is the original local homogeneous map. -/
theorem reesHomogeneousSections_app (n : ℕ) (U : X.affineOpens)
    (m : powerSections I f F n U.val) :
    (reesPushforwardSectionsIso I f F).hom.app (op U.val)
      ((reesHomogeneousSections I f F n).app (op U.val) m) =
      homogeneousSectionMap I f F n U.val U.property m := by
  change (reesPushforwardSectionsIso I f F).hom.app (op U.val)
    ((reesPowerSectionsIso I f F).hom.app (op U.val) _) = _
  rw [reesPowerSectionsIso, moduleSectionsIsoOfAffine_hom_app]
  exact reesPowerAffineSectionsIso_ι I f F U n m

/-- Every actual homogeneous coefficient multiplication intertwines the global
comparison with the original structural Rees action, on all opens. -/
theorem reesHomogeneousSections_mul (r n : ℕ) (a : ↥(I ^ r)) :
    (moduleSectionsPresheafFunctor X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).map
      (Modules.idealPowerMul X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) F I r n a) ≫
        reesHomogeneousSections I f F (r + n) =
      reesHomogeneousSections I f F n ≫
        (moduleSectionsPresheafFunctor X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).map
          ((Modules.pushforward (projection I f)).map
            (Modules.globalScalarEndomorphism (space I f) (coefficient I f F)
              (((structureMap I f).appTop.hom.comp
                (Scheme.ΓSpecIso (CommRingCat.of (reesAlgebra I))).inv.hom)
                ⟨Polynomial.monomial r a.val, reesAlgebra.monomial_mem.mpr a.property⟩))) := by
  apply TopCat.Sheaf.hom_ext _
    (moduleSectionsSheaf X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (reesPushforwardCoefficient I f F)) (affineOpens_range_isBasis X)
  intro U
  ext m
  apply ((reesPushforwardSectionsIso I f F).app (op U.val)).toLinearEquiv.injective
  change (reesPushforwardSectionsIso I f F).hom.app (op U.val)
    ((reesHomogeneousSections I f F (r + n)).app (op U.val) _) = _
  rw [reesHomogeneousSections_app]
  change homogeneousSectionMap I f F (r + n) U.val U.property
    ((Modules.idealPowerMul X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      F I r n a).app U.val m) = _
  refine (homogeneousSectionMap_mul I f F r n a U.val U.property m).trans ?_
  let b : reesAlgebra I :=
    ⟨Polynomial.monomial r a.val, reesAlgebra.monomial_mem.mpr a.property⟩
  have h := congrArg (fun x : coefficientSections I f F U.val => b • x)
    (reesHomogeneousSections_app I f F n U m).symm
  refine h.trans ?_
  change b • (show coefficientSections I f F U.val from
      (reesPushforwardSectionsIso I f F).hom.app (op U.val)
        ((reesHomogeneousSections I f F n).app (op U.val) m)) =
    (Modules.globalScalarEndomorphism (space I f) (coefficient I f F)
      (((structureMap I f).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of (reesAlgebra I))).inv.hom) b)).app
          (projection I f ⁻¹ᵁ U.val) _
  exact (Modules.globalScalarEndomorphism_app _ _ _ _ _).symm

end AlgebraicGeometry.Scheme.Cohomology
