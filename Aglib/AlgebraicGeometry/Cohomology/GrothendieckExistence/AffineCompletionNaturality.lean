/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompletionSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineFormalSectionsFunctor
public import Aglib.RingTheory.AdicCompletion.HomNaturality

/-! # Original affine completion coordinates commute with algebraic maps -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable (B : CommRingCat.{u}) [IsNoetherianRing B]
  (K : (Spec B).IdealSheafData) {G H : (Spec B).CoherentSheaf}

/-- Completion coordinates retain the actual completed algebraic map and
all original quotient units. -/
theorem affineCompletionSectionsEquiv_naturality (a : G ⟶ H) :
    let := ((completionFunctor (Spec B) K).obj G).affineFormalSectionsModule
    let := ((completionFunctor (Spec B) K).obj H).affineFormalSectionsModule
    (AdicSystem.affineFormalSectionsMap ((completionFunctor (Spec B) K).map a)).comp
      (affineCompletionSectionsEquiv B K G).toLinearMap =
    (affineCompletionSectionsEquiv B K H).toLinearMap.comp
      (AdicCompletion.map (affineIdeal B K) (moduleSpecΓFunctor.map a.hom).hom) := by
  let := ((completionFunctor (Spec B) K).obj G).affineFormalSectionsModule
  let := ((completionFunctor (Spec B) K).obj H).affineFormalSectionsModule
  let : Module.Finite B (moduleSpecΓFunctor.obj G.obj) :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B G.obj).mp G.property).2
  apply AdicCompletion.linearMap_ext_of_finite (affineIdeal B K)
  intro x
  apply Subtype.ext
  funext n
  change moduleSpecΓFunctor.map
      ((idealSheafQuotientFunctor (Spec B) (K ^ n.unop)).map a.hom)
        ((affineCompletionSectionsEquiv B K G
          (AdicCompletion.of (affineIdeal B K) _ x)).val n) =
    (affineCompletionSectionsEquiv B K H
      (AdicCompletion.map (affineIdeal B K) (moduleSpecΓFunctor.map a.hom).hom
        (AdicCompletion.of (affineIdeal B K) _ x))).val n
  rw [AdicCompletion.map_of, affineCompletionSectionsEquiv_of,
    affineCompletionSectionsEquiv_of]
  change moduleSpecΓFunctor.map
      ((idealSheafQuotientFunctor (Spec B) (K ^ n.unop)).map a.hom)
        (moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app G.obj) x) =
    moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B) (K ^ n.unop)).app H.obj)
      (moduleSpecΓFunctor.map a.hom x)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← (idealSheafQuotientUnit (Spec B) (K ^ n.unop)).naturality]
  rfl

end AlgebraicGeometry.Scheme.Modules.Coherent
