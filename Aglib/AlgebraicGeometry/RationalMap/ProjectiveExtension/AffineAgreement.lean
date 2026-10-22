/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.AffineBlowup
public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.UnitCoordinates
public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.UnitIdeal
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource.Naturality

/-!
# Actual agreement on the unit locus of affine coordinate ideals

The native coordinate-blowup map restricts to the projective map of the
original scalar coordinates. All section maps and unit comparisons are
retained; no agreement hypothesis or projective-class substitution occurs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.ProjectiveSpace.FromSections

universe u

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable (A : Type u) [CommRing A] {I : Type u} [Finite I] (v : I → A)

/-- The original affine coordinates, expressed as sections of the actual
invertible image ideal on the native blowup. -/
def affineBlowupSection (i : I) :=
  (pullbackUnitIso (Blowup.blowupDatum
    (Blowup.affineCenter A (affineCoordinateIdeal A v))).map).inv ≫
  lineSourcePulledCoordinate (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    (Blowup.affineCenter A (affineCoordinateIdeal A v)) (affineCoordinate A v)
    (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map i

instance affineBlowupSection_epi : Epi (Sigma.desc (affineBlowupSection A v)) := by
  let : Epi (Sigma.desc (affineCoordinate A v)) := affineCoordinate_epi A v
  exact LineSource.trivializedFamily_epi _ (pullbackUnitIso _) _ _

omit [Finite I] in
/-- Inclusion recovers literal multiplication by the original ring scalar. -/
@[reassoc]
theorem affineBlowupSection_inclusion (i : I) :
    affineBlowupSection A v i ≫
      Hom.idealInclusion ((Blowup.affineCenter A (affineCoordinateIdeal A v)).comap
        (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map).subschemeι =
    pullbackUnitEnd (Blowup.blowupDatum
      (Blowup.affineCenter A (affineCoordinateIdeal A v))).map
      (Blowup.IdealFrames.affineMultiplication A (v i)) := by
  have hi : affineCoordinate A v i ≫
      Hom.idealInclusion (Blowup.affineCenter A (affineCoordinateIdeal A v)).subschemeι =
      Blowup.IdealFrames.affineMultiplication A (v i) := by
    rw [affineCoordinate_inclusion, Blowup.IdealFrames.affineMultiplication]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact mul_comm a (v i)
  have hc := lineSourcePulledCoordinate_inclusion
    (SheafOfModules.unit (Spec (.of A)).ringCatSheaf)
    (Blowup.affineCenter A (affineCoordinateIdeal A v)) (affineCoordinate A v)
    (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map i
  rw [hi] at hc
  simpa only [affineBlowupSection, pullbackUnitEnd, Category.assoc] using
    congrArg (fun k ↦ (pullbackUnitIso (Blowup.blowupDatum
      (Blowup.affineCenter A (affineCoordinateIdeal A v))).map).inv ≫ k) hc

variable {R : Type u} [CommRing R] (p : Spec (.of A) ⟶ Spec (.of R))

/-- The actual line-source construction is the ordinary section construction
for these very sections. -/
theorem affineCoordinateBlowupMap_eq_sections :
    affineCoordinateBlowupMap A v p =
      mapOfFiniteFamily
        ((Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map ≫ p)
        _ (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).cartier
        (affineBlowupSection A v) := by
  let : Epi (Sigma.desc (affineCoordinate A v)) := affineCoordinate_epi A v
  exact LineSource.mapOfFamily_eq_of_sourceIso _ _ (pullbackUnitIso _) _ _ _ _

variable {S : Type u} [CommRing S]
variable (j : Spec (.of S) ⟶
  (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).Y)
variable [IsOpenImmersion j]
variable (hK : ((Blowup.affineCenter A (affineCoordinateIdeal A v)).comap
  (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map).comap j = ⊤)

/-- Literal original scalars pulled through the composite to the affine base. -/
def affineRestrictedScalar (i : I) :=
  pullbackUnitEnd (j ≫
    (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map)
    (Blowup.IdealFrames.affineMultiplication A (v i))

omit [Finite I] in
/-- Exact section equality in the canonical target frame. -/
theorem affineBlowupSection_restrict (i : I) :
    pulledFamily j (affineBlowupSection A v) i ≫ (unitLocusIdealIso _ j hK).hom =
      affineRestrictedScalar A v j i := by
  rw [unitLocusIdealIso_hom]
  change (pullbackUnitIso j).inv ≫
    (Scheme.Modules.pullback j).map (affineBlowupSection A v i) ≫
    (Scheme.Modules.pullback j).map (Hom.idealInclusion _) ≫ (pullbackUnitIso j).hom = _
  rw [← Functor.map_comp_assoc, affineBlowupSection_inclusion]
  exact (pullbackUnitEnd_comp j _ _).symm

include hK in
/-- The actual scalar row is generating on the prescribed unit locus. -/
theorem affineRestrictedScalar_epi :
    Epi (Sigma.desc (affineRestrictedScalar A v j)) := by
  have heq : (fun i ↦ pulledFamily j (affineBlowupSection A v) i ≫
      (unitLocusIdealIso _ j hK).hom) = affineRestrictedScalar A v j :=
    funext (affineBlowupSection_restrict A v j hK)
  rw [← heq]
  infer_instance

/-- Equality of the actual projective scheme morphisms on the prescribed open. -/
theorem affineCoordinateBlowupMap_restrict :
    letI : Epi (Sigma.desc (affineRestrictedScalar A v j)) :=
      affineRestrictedScalar_epi A v j hK
    j ≫ affineCoordinateBlowupMap A v p =
      mapOfFiniteFamily
        (j ≫ (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map ≫ p)
        (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
        (affineUnit_locallyRankOne S) (affineRestrictedScalar A v j) := by
  let : Epi (Sigma.desc (affineRestrictedScalar A v j)) :=
    affineRestrictedScalar_epi A v j hK
  rw [affineCoordinateBlowupMap_eq_sections]
  have heq : (fun i ↦ pulledFamily j (affineBlowupSection A v) i ≫
      (unitLocusIdealIso _ j hK).hom) = affineRestrictedScalar A v j :=
    funext (affineBlowupSection_restrict A v j hK)
  simpa only [heq] using mapOfFiniteFamily_pullback_iso j
    ((Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).map ≫ p)
    _ (Blowup.blowupDatum (Blowup.affineCenter A (affineCoordinateIdeal A v))).cartier
    (affineBlowupSection A v) _ (unitLocusIdealIso _ j hK)

end AlgebraicGeometry.Scheme.RationalCoordinates
