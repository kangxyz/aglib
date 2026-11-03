/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FlatBaseChange.QuotientChart
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Pushout
public import Aglib.AlgebraicGeometry.Spec.Localization

/-!
# The literal target quotient in a principal refinement

A genuine equality of mapped ideals proves the Cartesian square for the
original quotientMap. The target quotient and its original quotient map
are retained. No comparison or presentation equivalence is constructed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

section Literal
variable {R S : CommRingCat.{u}} [Algebra R S]
  (I : Ideal R) (J : Ideal S) (hJ : I.map (algebraMap R S) = J)

include hJ in
/-- A structural mapped-ideal equality supplies the actual quotientMap domain condition. -/
theorem literalQuotient_le_comap : I ≤ J.comap (algebraMap R S) :=
  Ideal.map_le_iff_le_comap.mp hJ.le

/-- The actual quotientMap square is Cartesian for the literal target ideal. -/
theorem literalQuotient_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap J (algebraMap R S) (literalQuotient_le_comap I J hJ))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  subst J
  exact quotientChart_isPullback R S I

/-- Openness belongs to that same actual quotientMap by the actual Cartesian square. -/
theorem literalQuotient_isOpenImmersion
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R S)))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap J (algebraMap R S) (literalQuotient_le_comap I J hJ)))) :=
  MorphismProperty.of_isPullback (literalQuotient_isPullback I J hJ).flip inferInstance

/-- The quotient scalar action is the original quotientMap action. -/
theorem literalQuotient_scalarTower :
    letI : Algebra (R ⧸ I) (S ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap (literalQuotient_le_comap I J hJ)
    IsScalarTower R (R ⧸ I) (S ⧸ J) := by
  subst J
  infer_instance

/-- The existing quotient pushout applies to the literal target ideal/action. -/
theorem literalQuotient_isPushout :
    letI : Algebra (R ⧸ I) (S ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap (literalQuotient_le_comap I J hJ)
    letI : IsScalarTower R (R ⧸ I) (S ⧸ J) := literalQuotient_scalarTower I J hJ
    Algebra.IsPushout R S (R ⧸ I) (S ⧸ J) := by
  subst J
  exact quotientFlatChart_isPushout I

/-- The existing pushout source iso preserves the literal original quotientMap unit. -/
theorem literalQuotient_source_unit (x : R ⧸ I) :
    letI : Algebra (R ⧸ I) (S ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap (literalQuotient_le_comap I J hJ)
    letI : IsScalarTower R (R ⧸ I) (S ⧸ J) := literalQuotient_scalarTower I J hJ
    letI : Algebra.IsPushout R S (R ⧸ I) (S ⧸ J) := literalQuotient_isPushout I J hJ
    (ModuleCat.scalarExtensionPushoutIso R S (R ⧸ I) (S ⧸ J)).hom
        ((1 : S) ⊗ₜ[R,algebraMap R S] x) =
      Ideal.quotientMap J (algebraMap R S) (literalQuotient_le_comap I J hJ) x := by
  let : Algebra (R ⧸ I) (S ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (literalQuotient_le_comap I J hJ)
  let : IsScalarTower R (R ⧸ I) (S ⧸ J) := literalQuotient_scalarTower I J hJ
  let : Algebra.IsPushout R S (R ⧸ I) (S ⧸ J) := literalQuotient_isPushout I J hJ
  exact ModuleCat.scalarExtensionPushoutIso_one_tmul R S (R ⧸ I) (S ⧸ J) x

end Literal

section Principal
variable {R S : CommRingCat.{u}} [Algebra R S] (I : Ideal R) (t : R)

local notation "Rₜ" => Localization.Away t
local notation "Sₜ" => Localization.Away (algebraMap R S t)
local notation "αₜ" => IsLocalization.Away.map Rₜ Sₜ (algebraMap R S) t

/-- The two original ambient localization paths have the same ring homomorphism. -/
theorem principalRefinement_ringSquare :
    RingHom.comp αₜ (algebraMap R Rₜ) =
      (algebraMap S Sₜ).comp (algebraMap R S) := by
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, IsLocalization.Away.map, IsLocalization.map_eq]

/-- The actual refined target ideal equals the image of the actual original target ideal. -/
theorem principalRefinement_targetIdeal :
    (I.map ((algebraMap S Sₜ).comp (algebraMap R S))) =
      (I.map (algebraMap R Rₜ)).map αₜ := by
  rw [Ideal.map_map, principalRefinement_ringSquare]

/-- The original target principal restriction uses this proved mapped-ideal equality. -/
theorem principalRefinement_targetIdeal_map :
    (I.map (algebraMap R S)).map (algebraMap S Sₜ) =
      (I.map (algebraMap R Rₜ)).map αₜ := by
  rw [Ideal.map_map]
  exact principalRefinement_targetIdeal I t

/-- The target source restriction is the original quotientMap into the literal
refined target ideal; its Cartesian square is proved, not provided. -/
theorem principalRefinement_targetSource_isPullback :
    let J := I.map (algebraMap R S)
    let Jₜ := (I.map (algebraMap R Rₜ)).map αₜ
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap Jₜ (algebraMap S Sₜ)
          (literalQuotient_le_comap (R := S) (S := CommRingCat.of Sₜ) J Jₜ
            (principalRefinement_targetIdeal_map I t)))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk Jₜ)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Spec.map (CommRingCat.ofHom (algebraMap S Sₜ))) :=
  literalQuotient_isPullback (R := S) (S := CommRingCat.of Sₜ) (I.map (algebraMap R S))
    ((I.map (algebraMap R Rₜ)).map αₜ) (principalRefinement_targetIdeal_map I t)

/-- The same literal target source restriction is open. -/
theorem principalRefinement_targetSource_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap ((I.map (algebraMap R Rₜ)).map αₜ) (algebraMap S Sₜ)
        (literalQuotient_le_comap (R := S) (S := CommRingCat.of Sₜ) (I.map (algebraMap R S))
          ((I.map (algebraMap R Rₜ)).map αₜ) (principalRefinement_targetIdeal_map I t))))) :=
  literalQuotient_isOpenImmersion (R := S) (S := CommRingCat.of Sₜ) (I.map (algebraMap R S))
    ((I.map (algebraMap R Rₜ)).map αₜ) (principalRefinement_targetIdeal_map I t)

end Principal
end AlgebraicGeometry.Scheme.Modules
