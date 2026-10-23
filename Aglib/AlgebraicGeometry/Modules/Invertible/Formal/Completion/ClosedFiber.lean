/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Approximation.Bridge
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.IdealSheaf
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# The original ideal fibre inside the actual completion base change

The original completion evaluation is a surjective quotient map with the
original extended ideal as kernel. Its actual base change identifies the
original ideal fibre with the completed scheme's actual ideal thickening.
The comparison retains the original map into the completed scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)

/-- The original structure map of the actual completion base change. -/
abbrev completionStructure : completionBaseChange f I ⟶
    Spec (CommRingCat.of (AdicCompletion I R)) :=
  Limits.pullback.fst (Spec.algebraMap R (AdicCompletion I R)) f

/-- The original closed-fibre map is the actual base change of the original
completion evaluation, over the original quotient spectrum. -/
theorem completionClosedFiberMap_isPullback :
    IsPullback (completionClosedFiberMap f I) (idealThickeningStructure f I)
      (completionStructure f I)
      (Spec.map (CommRingCat.ofHom (AdicCompletion.evalOneₐ I).toRingHom)) := by
  apply IsPullback.of_right _ (closedFiberCoefficientMap_fst f I (AdicCompletion.evalOneₐ I))
    (IsPullback.of_hasPullback (Spec.algebraMap R (AdicCompletion I R)) f).flip
  rw [closedFiberCoefficientMap_snd, specAlgHom_over]
  exact IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- The original completion closed-fibre map is a closed immersion. -/
instance completionClosedFiberMap_isClosedImmersion :
    IsClosedImmersion (completionClosedFiberMap f I) := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (AdicCompletion.evalOneₐ I).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (AdicCompletion.evalOneₐ_surjective I)
  exact MorphismProperty.of_isPullback (completionClosedFiberMap_isPullback f I).flip
    inferInstance

/-- The native completion quotient comparison identifies the two actual
spectral kernel ideal sheaves. -/
theorem completion_evalOne_spec_ker (hI : I.FG) :
    (Spec.map (CommRingCat.ofHom (AdicCompletion.evalOneₐ I).toRingHom)).ker =
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I.map (algebraMap R (AdicCompletion I R)))))).ker := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.specMap_kernel_top, Scheme.IdealSheafData.specMap_kernel_top,
    AdicCompletion.ker_evalOneₐ_eq_map I hI, Ideal.mk_ker]

/-- The original closed fibre and the completed extended-ideal thickening
have exactly the same intrinsic kernel inside the actual completed scheme. -/
theorem completionClosedFiberMap_ker (hI : I.FG) :
    (completionClosedFiberMap f I).ker =
      (idealThickeningι (completionStructure f I)
        (I.map (algebraMap R (AdicCompletion I R)))).ker := by
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (AdicCompletion.evalOneₐ I).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (AdicCompletion.evalOneₐ_surjective I)
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I.map (algebraMap R (AdicCompletion I R)))))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let H := completionClosedFiberMap_isPullback f I
  have he := congrArg Scheme.Hom.ker H.isoPullback_hom_fst
  rw [Scheme.Hom.ker_comp_of_isIso] at he
  rw [← he, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    completion_evalOne_spec_ker I hI]
  exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I.map (algebraMap R (AdicCompletion I R))))))
    (completionStructure f I)).symm

/-- Canonical identification of the original ideal fibre with the actual
extended-ideal fibre of the actual completion base change. -/
def completionClosedFiberIso (hI : I.FG) :
    idealThickeningSpace f I ≅
      idealThickeningSpace (completionStructure f I)
        (I.map (algebraMap R (AdicCompletion I R))) := by
  let i := idealThickeningι (completionStructure f I)
    (I.map (algebraMap R (AdicCompletion I R)))
  let k := completionClosedFiberMap f I
  let a := IsClosedImmersion.lift i k (completionClosedFiberMap_ker f I hI).ge
  have : IsIso a := IsClosedImmersion.isIso_of_ker_eq k i a
    (IsClosedImmersion.lift_fac _ _ _) (completionClosedFiberMap_ker f I hI)
  exact asIso a

/-- The canonical comparison preserves the original closed-fibre immersion
into the completed scheme. -/
@[reassoc (attr := simp)]
theorem completionClosedFiberIso_hom_ι (hI : I.FG) :
    (completionClosedFiberIso f I hI).hom ≫
      idealThickeningι (completionStructure f I)
        (I.map (algebraMap R (AdicCompletion I R))) = completionClosedFiberMap f I := by
  simp [completionClosedFiberIso]

@[reassoc (attr := simp)]
theorem completionClosedFiberIso_inv_map (hI : I.FG) :
    (completionClosedFiberIso f I hI).inv ≫ completionClosedFiberMap f I =
      idealThickeningι (completionStructure f I)
        (I.map (algebraMap R (AdicCompletion I R))) := by
  apply (cancel_epi (completionClosedFiberIso f I hI).hom).mp
  simp

/-- A restriction comparison on the completed extended-ideal fibre gives an
actual restriction comparison on the original ideal fibre. -/
def completionClosedFiberRestrictionIso (hI : I.FG)
    (M : (completionBaseChange f I).Modules) (L : (idealThickeningSpace f I).Modules)
    (e : (pullback (idealThickeningι (completionStructure f I)
        (I.map (algebraMap R (AdicCompletion I R))))).obj M ≅
      (pullback (completionClosedFiberIso f I hI).inv).obj L) :
    (pullback (completionClosedFiberMap f I)).obj M ≅ L :=
  ((pullbackTriangleIso (completionClosedFiberIso f I hI).hom
    (idealThickeningι (completionStructure f I) (I.map (algebraMap R (AdicCompletion I R))))
    (completionClosedFiberMap f I) (completionClosedFiberIso_hom_ι f I hI)).app M).symm ≪≫
    (pullback (completionClosedFiberIso f I hI).hom).mapIso e ≪≫
    (pullbackComp (completionClosedFiberIso f I hI).hom
      (completionClosedFiberIso f I hI).inv).app L ≪≫
    (pullbackCongr (completionClosedFiberIso f I hI).hom_inv_id).app L ≪≫
    (pullbackId _).app L

end AlgebraicGeometry.Scheme.Modules.Invertible
