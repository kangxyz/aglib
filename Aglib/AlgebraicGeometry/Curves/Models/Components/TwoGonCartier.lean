/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Models.Components.Cartier
public import Aglib.AlgebraicGeometry.Curves.Models.Components.Intersections
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Restriction
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedClosedUnion
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.DegreeIso
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.AffineDegree
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor

/-!
# Cartier ideals and degree-two intersections of the literal two-gon

Source: frozen R5 `LocalModels/Incidence/Cartier.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original actual schemes, kernel ideals and structural triangles are retained.
Unused model wrappers are replaced by the actual scheme and map parameters.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules.Invertible
open Scheme.Hom
open Scheme.Hom.Cartier
open Scheme.IdealSheafData
universe u
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))

/-- The left closed component of the actual two-gon fibre is integral. -/
instance leftComponent_integral (e : TwoGonIso π) : IsIntegral (twoGonLeftComponentScheme π e) :=
  IsIntegral.of_isIso (twoGonLeftComponentMap π e).toImage

/-- The right closed component of the actual two-gon fibre is integral. -/
instance rightComponent_integral (e : TwoGonIso π) : IsIntegral (twoGonRightComponentScheme π e) :=
  IsIntegral.of_isIso (twoGonRightComponentMap π e).toImage

theorem leftComponent_range_irreducible (e : TwoGonIso π) :
    Set.range (twoGonLeftComponentMap π e).imageι ∈ irreducibleComponents (obj π) := by
  rw [twoGonLeftComponentScheme_range, twoGon_components_eq]
  exact Set.mem_insert _ _

theorem rightComponent_range_irreducible (e : TwoGonIso π) :
    Set.range (twoGonRightComponentMap π e).imageι ∈ irreducibleComponents (obj π) := by
  rw [twoGonRightComponentScheme_range, twoGon_components_eq]
  exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
/-- The actual closed left component immersion into the ambient model. -/
abbrev leftSurfaceMap (e : TwoGonIso π) : twoGonLeftComponentScheme π e ⟶ Y :=
  (twoGonLeftComponentMap π e).imageι ≫ (projection π)

/-- The actual closed right component immersion into the ambient model. -/
abbrev rightSurfaceMap (e : TwoGonIso π) : twoGonRightComponentScheme π e ⟶ Y :=
  (twoGonRightComponentMap π e).imageι ≫ (projection π)

theorem componentSurface_ranges_cover (e : TwoGonIso π) :
    Set.range (leftSurfaceMap π e) ∪ Set.range (rightSurfaceMap π e) =
      Set.range (projection π) := by
  change Set.range ((projection π) ∘ (twoGonLeftComponentMap π e).imageι) ∪
    Set.range ((projection π) ∘ (twoGonRightComponentMap π e).imageι) = _
  rw [Set.range_comp, Set.range_comp, ← Set.image_union,
    twoGonLeftComponentScheme_range, twoGonRightComponentScheme_range,
    twoGon_components_cover, Set.image_univ]

/-- The actual reduced-fibre ideal is the intersection of the two actual
ambient component ideals. Multiplication is a separate Cartier step. -/
theorem reducedFibreIdeal_eq_inf (e : TwoGonIso π) :
    (projection π).ker = (leftSurfaceMap π e).ker ⊓ (rightSurfaceMap π e).ker := by
  let := twoGon_specialFiber_reduced π e
  exact reduced_closed_union_ideal (projection π) (leftSurfaceMap π e)
    (rightSurfaceMap π e) (componentSurface_ranges_cover π e)

/-- Actual component images cannot be contained in one another. -/
theorem leftSurface_not_subset_right (e : TwoGonIso π) :
    ¬ Set.range (leftSurfaceMap π e) ⊆ Set.range (rightSurfaceMap π e) := by
  intro h
  change Set.range ((projection π) ∘ (twoGonLeftComponentMap π e).imageι) ⊆
    Set.range ((projection π) ∘ (twoGonRightComponentMap π e).imageι) at h
  rw [Set.range_comp, Set.range_comp,
    Set.image_subset_image_iff (projection π).isClosedEmbedding.injective,
    twoGonLeftComponentScheme_range, twoGonRightComponentScheme_range] at h
  exact Scheme.TwoGon.target_left_not_subset_right _
    (e.hom.left.homeomorph.surjective.preimage_subset_preimage_iff.mp h)

theorem rightSurface_not_subset_left (e : TwoGonIso π) :
    ¬ Set.range (rightSurfaceMap π e) ⊆ Set.range (leftSurfaceMap π e) := by
  intro h
  change Set.range ((projection π) ∘ (twoGonRightComponentMap π e).imageι) ⊆
    Set.range ((projection π) ∘ (twoGonLeftComponentMap π e).imageι) at h
  rw [Set.range_comp, Set.range_comp,
    Set.image_subset_image_iff (projection π).isClosedEmbedding.injective,
    twoGonRightComponentScheme_range, twoGonLeftComponentScheme_range] at h
  exact Scheme.TwoGon.target_right_not_subset_left _
    (e.hom.left.homeomorph.surjective.preimage_subset_preimage_iff.mp h)
/-- The residue-field structure map of the left closed component. -/
abbrev leftComponentStructure (e : TwoGonIso π) :
    twoGonLeftComponentScheme π e ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
  (twoGonLeftComponentMap π e).imageι ≫ (structureMap π)

/-- The residue-field structure map of the right closed component. -/
abbrev rightComponentStructure (e : TwoGonIso π) :
    twoGonRightComponentScheme π e ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
  (twoGonRightComponentMap π e).imageι ≫ (structureMap π)

/-- The two surface-intersection projections induce the same residue-field
structure, derived by cancellation of the closed residue immersion. -/
theorem intersection_structure_eq (e : TwoGonIso π) :
    pullback.fst (leftSurfaceMap π e) (rightSurfaceMap π e) ≫ leftComponentStructure π e =
      pullback.snd (leftSurfaceMap π e) (rightSurfaceMap π e) ≫ rightComponentStructure π e := by
  apply (cancel_mono (Scheme.LocalRing.residueSpecMap R)).mp
  simp only [Category.assoc, leftComponentStructure, rightComponentStructure]
  rw [← pullback.condition]
  change pullback.fst (leftSurfaceMap π e) (rightSurfaceMap π e) ≫ leftSurfaceMap π e ≫ π =
    pullback.snd (leftSurfaceMap π e) (rightSurfaceMap π e) ≫ rightSurfaceMap π e ≫ π
  simpa only [Category.assoc] using congrArg (fun f => f ≫ π)
    (pullback.condition (f := leftSurfaceMap π e) (g := rightSurfaceMap π e))

/-- Actual degree two on the global model-surface intersection, with the
existing affine calculation transported over the actual residue field. -/
theorem surfaceIntersection_degree (e : TwoGonIso π) :
    Scheme.Hom.finiteSchemeDegree (IsLocalRing.ResidueField R)
      (twoGonSurfaceIntersectionStructure π e) = 2 := by
  rw [finiteSchemeDegree_iso _ _ (twoGonSurfaceIntersectionIsoTwoPoints π e)
    (twoGonSurfaceIntersectionIsoTwoPoints_over π e)]
  exact Scheme.Hom.twoPointSchemeDegree _

theorem rightIntersection_degree (e : TwoGonIso π) :
    Scheme.Hom.finiteSchemeDegree (IsLocalRing.ResidueField R)
      (pullback.snd (leftSurfaceMap π e) (rightSurfaceMap π e) ≫ rightComponentStructure π e) =
        2 := by
  rw [← intersection_structure_eq]
  exact surfaceIntersection_degree π e

/-- The surface intersection, projected to the right component, is finite over the residue field. -/
instance rightIntersection_finite (e : TwoGonIso π) :
    IsFinite (pullback.snd (leftSurfaceMap π e) (rightSurfaceMap π e) ≫ rightComponentStructure
      π e) := by
  rw [← intersection_structure_eq]
  exact twoGonSurfaceIntersection_finite π e

theorem leftIntersection_degree (e : TwoGonIso π) :
    Scheme.Hom.finiteSchemeDegree (IsLocalRing.ResidueField R)
      (pullback.snd (rightSurfaceMap π e) (leftSurfaceMap π e) ≫ leftComponentStructure π e) =
        2 := by
  rw [finiteSchemeDegree_iso _ _ (pullbackSymmetry (rightSurfaceMap π e) (leftSurfaceMap π e))]
  · exact surfaceIntersection_degree π e
  · simp [twoGonSurfaceIntersectionStructure, leftComponentStructure]

/-- The surface intersection, projected to the left component, is finite over the residue field. -/
instance leftIntersection_finite (e : TwoGonIso π) :
    IsFinite (pullback.snd (rightSurfaceMap π e) (leftSurfaceMap π e) ≫ leftComponentStructure
      π e) := by
  have he : pullback.snd (rightSurfaceMap π e) (leftSurfaceMap π e) ≫ leftComponentStructure π e =
      (pullbackSymmetry (rightSurfaceMap π e) (leftSurfaceMap π e)).hom ≫
        twoGonSurfaceIntersectionStructure π e := by
    simp [twoGonSurfaceIntersectionStructure, leftComponentStructure]
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
section Cartier
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y] (π : Y ⟶ Spec (.of R)) [Flat π]

/-- Actual left component Cartier bundle obtained by proved applicability. -/
def leftComponentIdealLineBundle
    (hcartier : RegularCodimOneIdealInvertible.{u})
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (e : TwoGonIso π) :
      LineBundle Y :=
  componentIdealLineBundle π hcartier hregular (twoGonLeftComponentMap π e).imageι
    (leftComponent_range_irreducible π e)

/-- Actual right component Cartier bundle obtained by proved applicability. -/
def rightComponentIdealLineBundle
    (hcartier : RegularCodimOneIdealInvertible.{u})
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (e : TwoGonIso π) :
      LineBundle Y :=
  componentIdealLineBundle π hcartier hregular (twoGonRightComponentMap π e).imageι
    (rightComponent_range_irreducible π e)

variable (hcartier : RegularCodimOneIdealInvertible.{u})
  (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
  (havoid : IntegralAvoidanceCartierPullback.{u})
include hcartier hregular havoid

/-- The left component ideal restricted to the right component, identified with the intersection
ideal using the supplied Cartier and avoidance inputs. -/
def rightCrossIdealIso (e : TwoGonIso π) :
    (pullbackLineBundle (rightSurfaceMap π e)
      (leftComponentIdealLineBundle π hcartier hregular e)).val ≅
        idealModule (pullback.snd (leftSurfaceMap π e) (rightSurfaceMap π e)) :=
  cartierRestrictionIso havoid _ _
    (leftComponentIdealLineBundle π hcartier hregular e).property
    (rightSurface_not_subset_left π e)

/-- The right component ideal restricted to the left component, identified with the intersection
ideal using the supplied Cartier and avoidance inputs. -/
def leftCrossIdealIso (e : TwoGonIso π) :
    (pullbackLineBundle (leftSurfaceMap π e)
      (rightComponentIdealLineBundle π hcartier hregular e)).val ≅
        idealModule (pullback.snd (rightSurfaceMap π e) (leftSurfaceMap π e)) :=
  cartierRestrictionIso havoid _ _
    (rightComponentIdealLineBundle π hcartier hregular e).property
    (leftSurface_not_subset_right π e)

theorem rightIntersection_ideal_invertible (e : TwoGonIso π) :
    IsLocallyRankOne (twoGonRightComponentScheme π e)
      (idealModule (pullback.snd (leftSurfaceMap π e) (rightSurfaceMap π e))) :=
  cartierRestriction_invertible havoid _ _
    (leftComponentIdealLineBundle π hcartier hregular e).property
    (rightSurface_not_subset_left π e)

theorem leftIntersection_ideal_invertible (e : TwoGonIso π) :
    IsLocallyRankOne (twoGonLeftComponentScheme π e)
      (idealModule (pullback.snd (rightSurfaceMap π e) (leftSurfaceMap π e))) :=
  cartierRestriction_invertible havoid _ _
    (rightComponentIdealLineBundle π hcartier hregular e).property
    (leftSurface_not_subset_right π e)

/-- Principal reduced-fibre product identity, on the actual native ideal
sheaf data. Reducedness and exhaustive coverage were proved independently. -/
theorem componentIdealProduct_eq_fibre (hunion : CartierSumIdealEqualsUnion.{u})
    (e : TwoGonIso π) :
    (leftSurfaceMap π e).ker * (rightSurfaceMap π e).ker = (projection π).ker := by
  rw [hunion Y _ _ (leftSurfaceMap π e) (rightSurfaceMap π e)
    inferInstance inferInstance
    (leftComponentIdealLineBundle π hcartier hregular e).property
    (rightComponentIdealLineBundle π hcartier hregular e).property
    (rightIntersection_ideal_invertible π hcartier hregular havoid e)]
  exact (reducedFibreIdeal_eq_inf π e).symm

/-- Actual tensor product of component ideal bundles is the actual fibre
ideal module. No numerical equation is supplied. -/
def componentIdealTensorFibreIso (hunion : CartierSumIdealEqualsUnion.{u})
    (htensor : CartierIdealTensorProduct.{u}) (e : TwoGonIso π) :
    (tensorLineBundle Y (leftComponentIdealLineBundle π hcartier hregular e)
      (rightComponentIdealLineBundle π hcartier hregular e)).val ≅
        idealModule (projection π) :=
  (htensor Y _ _ (leftSurfaceMap π e) (rightSurfaceMap π e)
    inferInstance inferInstance
    (leftComponentIdealLineBundle π hcartier hregular e).property
    (rightComponentIdealLineBundle π hcartier hregular e).property).choose ≪≫
  eqToIso (congrArg (fun I : Y.IdealSheafData => idealModule I.subschemeι)
    (componentIdealProduct_eq_fibre π hcartier hregular havoid hunion e)) ≪≫
  idealImageIso (projection π)

/-- Principal uniformizer trivialization of that very tensor product. -/
def componentIdealTensorUnitIso (hunion : CartierSumIdealEqualsUnion.{u})
    (htensor : CartierIdealTensorProduct.{u}) (hprincipal : FlatDVRFibreIdealTrivial.{u})
    (e : TwoGonIso π) :
    (tensorLineBundle Y (leftComponentIdealLineBundle π hcartier hregular e)
      (rightComponentIdealLineBundle π hcartier hregular e)).val ≅
        SheafOfModules.unit Y.ringCatSheaf :=
  componentIdealTensorFibreIso π hcartier hregular havoid hunion htensor e ≪≫
    (hprincipal R Y π (inferInstance : Flat π)).some

/-- The Picard equality is an output of actual ideal/module constructions. -/
theorem componentIdealClasses_sum_zero (hunion : CartierSumIdealEqualsUnion.{u})
    (htensor : CartierIdealTensorProduct.{u}) (hprincipal : FlatDVRFibreIdealTrivial.{u})
    (e : TwoGonIso π) :
    classOf Y (leftComponentIdealLineBundle π hcartier hregular e) +
      classOf Y (rightComponentIdealLineBundle π hcartier hregular e) = 0 := by
  rw [← classOf_tensor]
  change classOf Y _ = classOf Y (trivialLineBundle Y)
  apply Quotient.sound
  exact ⟨componentIdealTensorUnitIso π hcartier hregular havoid hunion htensor hprincipal e ≪≫
    (coproductUniqueIso (fun _ : PUnit.{u+1} => SheafOfModules.unit Y.ringCatSheaf)).symm⟩

end Cartier
end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
