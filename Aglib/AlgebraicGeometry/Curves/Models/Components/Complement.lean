/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Models.Components.Minimality
public import Aglib.AlgebraicGeometry.Curves.Models.Components.Cartier
public import Aglib.AlgebraicGeometry.Curves.Models.Components.CartierUnions
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.RadicalSubscheme
public import Aglib.AlgebraicGeometry.Limits.PullbackTransport
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.DegreeIso
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.AffineDegree

/-!
# Actual complementary component unions and two-point intersections

The component index is the actual irreducible-component subtype of the literal residue fibre.
Kernel intersections define the reduced complement. All surface regularity, flatness, Cartier,
product, principal-fibre and degree inputs remain explicit, with the component-kernel premise
discharged by the existing native theorem. No model or contraction existence is constructed.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/LocalModels/Incidence/ComponentComplement.lean`: source ranges [[99, 422], [441, 460]];
SHA-256 `bd7461675195bb8fa659752b068eda53f895ecaac2b248d78669b1595736761b`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open Scheme.IdealSheafData Scheme.Hom Scheme.Hom.Cartier
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.OverField.Curve.Picard
open Scheme.Hom.ActualSpecialFiber
open Scheme.Pullback.GenericRestriction.SplitRationalComponents (pullbackCompMono_snd)
universe u

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
/-- Properness of the actual fibre structure gives finitely many irreducible components. -/
theorem components_finite {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) [IsProper π] :
    Finite (irreducibleComponents (obj π)) := by
  let : IsLocallyNoetherian (obj π) := LocallyOfFiniteType.isLocallyNoetherian (structureMap π)
  let : CompactSpace (obj π) := QuasiCompact.compactSpace_of_compactSpace (structureMap π)
  let : IsNoetherian (obj π) := ⟨⟩
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))
  {C : irreducibleComponents (obj π) → Scheme.{u}}
  (i : ∀ v, C v ⟶ obj π)
  [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))]
  (hrange : ∀ v, Set.range (i v) = v.val)

/-- The actual ideal intersection of all component kernels except the selected component. -/
def otherIdeal (v : irreducibleComponents (obj π)) : (obj π).IdealSheafData :=
  ⨅ w : {w : irreducibleComponents (obj π) // w ≠ v}, (i w.val).ker

/-- The closed union of the supports of all other actual components. -/
def otherSupport (v : irreducibleComponents (obj π)) : TopologicalSpace.Closeds (obj π) :=
  ⟨⋃ w : {w : irreducibleComponents (obj π) // w ≠ v}, w.val.val,
    isClosed_iUnion_of_finite (fun w => isClosed_of_mem_irreducibleComponents _ w.val.property)⟩

/-- The actual closed complement subscheme defined by the other component kernels. -/
abbrev otherScheme (v : irreducibleComponents (obj π)) : Scheme.{u} := (otherIdeal π i v).subscheme
/-- The canonical closed inclusion of the actual complementary component union. -/
abbrev otherMap (v : irreducibleComponents (obj π)) : otherScheme π i v ⟶ (obj π) :=
  (otherIdeal π i v).subschemeι
/-- The same complementary union included in the ambient scheme. -/
abbrev otherSurfaceMap (v : irreducibleComponents (obj π)) : otherScheme π i v ⟶ Y :=
  otherMap π i v ≫ (projection π)

include hrange in
/-- Exact ideal equality identifies the reduced complement scheme. -/
theorem otherIdeal_eq_vanishingIdeal (v : irreducibleComponents (obj π)) :
    otherIdeal π i v = vanishingIdeal (otherSupport π v) := by
  have hs : otherSupport π v =
      ⨆ w : {w : irreducibleComponents (obj π) // w ≠ v},
        (⟨w.val.val,isClosed_of_mem_irreducibleComponents _ w.val.property⟩ :
          TopologicalSpace.Closeds (obj π)) := by
    apply le_antisymm
    · rintro x hx
      rcases Set.mem_iUnion.mp hx with ⟨w,hw⟩
      exact le_iSup (fun w : {w : irreducibleComponents (obj π) // w ≠ v} =>
        (⟨w.val.val,isClosed_of_mem_irreducibleComponents _ w.val.property⟩ :
          TopologicalSpace.Closeds (obj π))) w hw
    · apply iSup_le
      intro w x hx
      exact Set.mem_iUnion.mpr ⟨w,hx⟩
  rw [hs,vanishingIdeal_iSup]
  unfold otherIdeal
  congr 1
  funext w
  exact kernel_eq_componentVanishingIdeal π i hrange w.val

include hrange in
theorem otherMap_range (v : irreducibleComponents (obj π)) :
    Set.range (otherMap π i v) =
      ⋃ w : {w : irreducibleComponents (obj π) // w ≠ v}, w.val.val := by
  rw [range_subschemeι,otherIdeal_eq_vanishingIdeal π i hrange]
  exact coe_support_vanishingIdeal _

/-- The complementary closed union is reduced because its ideal is radical. -/
instance otherScheme_reduced (v : irreducibleComponents (obj π)) :
    IsReduced (otherScheme π i v) := by
  apply Scheme.IdealSheafData.subscheme_reduced_of_radical
  ext U : 2
  change ((otherIdeal π i v).ideal U).radical = (otherIdeal π i v).ideal U
  simp only [otherIdeal, ideal_iInf, iInf_apply]
  apply Ideal.radical_eq_iff.mpr
  apply Ideal.isRadical_iInf
  intro w
  apply Ideal.radical_eq_iff.mp
  exact congrArg (fun J : (obj π).IdealSheafData => J.ideal U) (kernel_radical (i w.val))

/-- The original complementary union is closed in the original ambient scheme. -/
instance otherSurfaceMap_closed (v : irreducibleComponents (obj π)) :
    IsClosedImmersion (otherSurfaceMap π i v) := by
  unfold otherSurfaceMap otherMap
  infer_instance

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
include hrange in
theorem component_pairwise_not_subset : Pairwise (fun v w : irreducibleComponents (obj π) =>
    ¬ Set.range (i v) ⊆ Set.range (i w)) := by
  intro v w hvw h
  rw [hrange,hrange] at h
  exact hvw (Subtype.ext (Set.Subset.antisymm h (v.property.2 w.property.1 h)))

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
include hrange in
theorem surface_pairwise_not_subset : Pairwise (fun v w : irreducibleComponents (obj π) =>
    ¬ Set.range (surfaceInclusion π i v) ⊆ Set.range (surfaceInclusion π i w)) := by
  intro v w hvw h
  apply component_pairwise_not_subset π i hrange hvw
  change Set.range ((projection π) ∘ i v) ⊆
    Set.range ((projection π) ∘ i w) at h
  rwa [Set.range_comp,Set.range_comp,
    Set.image_subset_image_iff (projection π).isClosedEmbedding.injective] at h

include hrange in
theorem component_not_subset_other (v : irreducibleComponents (obj π)) :
    ¬ Set.range (i v) ⊆ Set.range (otherMap π i v) := by
  classical
  let := Fintype.ofFinite {w : irreducibleComponents (obj π) // w ≠ v}
  intro h
  rw [hrange,otherMap_range π i hrange] at h
  let s := Finset.univ.image (fun w : {w : irreducibleComponents (obj π) // w ≠ v} => w.val.val)
  have hc : ∀ z ∈ s, IsClosed z := by
    intro z hz
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hz
    exact isClosed_of_mem_irreducibleComponents _ w.val.property
  have hh : v.val ⊆ ⋃₀ (s : Set (Set (obj π))) := by simpa [s] using h
  obtain ⟨z,hz,hsub⟩ := isIrreducible_iff_sUnion_isClosed.mp v.property.1 s hc hh
  obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hz
  exact w.property (Subtype.ext (Set.Subset.antisymm hsub
    (v.property.2 w.val.property.1 hsub)).symm)

include hrange in
theorem surface_not_subset_other (v : irreducibleComponents (obj π)) :
    ¬ Set.range (surfaceInclusion π i v) ⊆ Set.range (otherSurfaceMap π i v) := by
  intro h
  apply component_not_subset_other π i hrange v
  change Set.range ((projection π) ∘ i v) ⊆
    Set.range ((projection π) ∘ otherMap π i v) at h
  rwa [Set.range_comp,Set.range_comp,
    Set.image_subset_image_iff (projection π).isClosedEmbedding.injective] at h

include hrange in
theorem component_and_others_cover (v : irreducibleComponents (obj π)) :
    Set.range (i v) ∪ Set.range (otherMap π i v) = Set.univ := by
  rw [hrange,otherMap_range π i hrange]
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨w,hw⟩ := exhaustive π i hrange x
  rw [hrange] at hw
  by_cases h : w = v
  · exact Or.inl (h ▸ hw)
  · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨w,h⟩,hw⟩)

include hrange in
theorem surface_ranges_cover (v : irreducibleComponents (obj π)) :
    Set.range (otherSurfaceMap π i v) ∪ Set.range (surfaceInclusion π i v) =
      Set.range (projection π) := by
  change Set.range ((projection π) ∘ otherMap π i v) ∪
    Set.range ((projection π) ∘ i v) = _
  rw [Set.range_comp,Set.range_comp,← Set.image_union,Set.union_comm,
    component_and_others_cover π i hrange,Set.image_univ]

include hrange in
theorem fibreIdeal_eq_inf [IsReduced (obj π)] (v : irreducibleComponents (obj π)) :
    (projection π).ker = (otherSurfaceMap π i v).ker ⊓ (surfaceInclusion π i v).ker :=
  reduced_closed_union_ideal (projection π) (otherSurfaceMap π i v) (surfaceInclusion π i v)
    (surface_ranges_cover π i hrange v)

omit [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))] in
theorem otherSurface_kernel (v : irreducibleComponents (obj π)) :
    (otherSurfaceMap π i v).ker =
      ⨅ w : {w : irreducibleComponents (obj π) // w ≠ v}, (surfaceInclusion π i w.val).ker := by
  rw [otherSurfaceMap,Scheme.Hom.ker_comp,ker_subschemeι,otherIdeal,
    (map_gc (projection π)).u_iInf]
  simp only [map_ker]

/-- The actual fibre product of a component and its complement inside the residue fibre. -/
abbrev componentOtherIntersection (v : irreducibleComponents (obj π)) : Scheme.{u} :=
  pullback (otherMap π i v) (i v)
/-- The structural map of that same fibre product to the original residue field. -/
abbrev componentOtherIntersectionStructure (v : irreducibleComponents (obj π)) :
    componentOtherIntersection π i v ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
  pullback.snd _ _ ≫ structureMap π i v

/-- This is an actual structural isomorphism of the native intersection. It is
source-specific applicability data, never a supplied numerical degree or count. -/
abbrev componentOtherTwoPointIso (v : irreducibleComponents (obj π)) :=
  Over.mk (componentOtherIntersectionStructure π i v) ≅
    Over.mk (Spec.algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R))

include hrange in
/-- Nonemptiness of the genuine intersection forces a genuinely different
component; no assumed component number is needed by Cartier-union induction. -/
theorem otherIndex_nonempty (v : irreducibleComponents (obj π))
    (e : componentOtherTwoPointIso π i v) :
    Nonempty {w : irreducibleComponents (obj π) // w ≠ v} := by
  let x : Spec (.of (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) :=
    Classical.choice inferInstance
  let y : componentOtherIntersection π i v := e.inv.left x
  have hy : (otherMap π i v) ((pullback.fst (otherMap π i v) (i v)) y) ∈ Set.range (otherMap π i
    v) := ⟨_,rfl⟩
  rw [otherMap_range π i hrange] at hy
  obtain ⟨w,_⟩ := Set.mem_iUnion.mp hy
  exact ⟨w⟩


end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y] (π : Y ⟶ Spec (.of R)) [Flat π]
  {C : irreducibleComponents (obj π) → Scheme.{u}}
  (i : ∀ v, C v ⟶ obj π)
  [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))]
  (hrange : ∀ v, Set.range (i v) = v.val)
  (q : ∀ v, Over.mk (structureMap π i v) ≅
    Over.mk (Scheme.ProjectiveLine.structureMap (IsLocalRing.ResidueField R)))
  (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
  (hcartier : RegularCodimOneIdealInvertible.{u})
  (havoid : IntegralAvoidanceCartierPullback.{u})
  (hunion : CartierSumIdealEqualsUnion.{u})
  (htensor : CartierIdealTensorProduct.{u})
  (hprincipal : FlatDVRFibreIdealTrivial.{u})
  (hdegree : Scheme.OverField.Curve.Abel.FiniteCartierIdealDegree.{u})
  (hprod : Degree.ProperCurveProductFormula.{u})

omit [Finite (irreducibleComponents (obj π))] in
include hrange hregular hcartier in
theorem surfaceIdeal_invertible (v : irreducibleComponents (obj π)) :
    IsLocallyRankOne Y (idealModule (surfaceInclusion π i v)) := by
  apply component_ideal_invertible π hcartier hregular (i v)
  rw [hrange]
  exact v.property

include hrange hregular hcartier havoid hunion htensor in
/-- The complementary native union is Cartier, derived from its actual finite
integral components and the actual nonempty two-endpoint intersection. -/
theorem otherSurfaceIdeal_invertible (v : irreducibleComponents (obj π))
    (e : componentOtherTwoPointIso π i v) :
    IsLocallyRankOne Y (idealModule (otherSurfaceMap π i v)) := by
  classical
  let := Fintype.ofFinite {w : irreducibleComponents (obj π) // w ≠ v}
  let := otherIndex_nonempty π i hrange v e
  have hc := iInfIdeal_cartier
    (fun w : {w : irreducibleComponents (obj π) // w ≠ v} => surfaceInclusion π i w.val)
    havoid hunion htensor
    (fun w => surfaceIdeal_invertible π i hrange hregular hcartier w.val)
    (fun a b hab => surface_pairwise_not_subset π i hrange
      (show a.val ≠ b.val from fun h => hab (Subtype.ext h)))
  rw [← otherSurface_kernel π i v] at hc
  exact isLocallyRankOne_of_iso Y (idealImageIso (otherSurfaceMap π i v)) hc

/-- The actual component-complement fibre product inside the ambient scheme. -/
abbrev surfaceIntersection (v : irreducibleComponents (obj π)) : Scheme.{u} :=
  pullback (otherSurfaceMap π i v) (surfaceInclusion π i v)
/-- The same ambient intersection over the original residue field. -/
abbrev surfaceIntersectionStructure (v : irreducibleComponents (obj π)) :
    surfaceIntersection π i v ⟶ Spec (.of (IsLocalRing.ResidueField R)) :=
  pullback.snd _ _ ≫ structureMap π i v


/-- The canonical comparison through the monomorphic residue-fibre inclusion. -/
def surfaceIntersectionIsoTwoPoints (v : irreducibleComponents (obj π))
    (e : componentOtherTwoPointIso π i v) :
    surfaceIntersection π i v ≅
      Spec (.of (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) :=
  pullbackCompMonoIso (otherMap π i v) (i v) (projection π) ≪≫
    (Over.forget _).mapIso e

omit [IsLocallyNoetherian Y] [Flat π] [∀ v, IsClosedImmersion (i v)]
  [∀ v, IsIntegral (C v)] [Finite (irreducibleComponents (obj π))] in
@[reassoc] theorem surfaceIntersectionIsoTwoPoints_over
    (v : irreducibleComponents (obj π)) (e : componentOtherTwoPointIso π i v) :
    (surfaceIntersectionIsoTwoPoints π i v e).hom ≫
      Spec.algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R) =
      surfaceIntersectionStructure π i v := by
  have he : e.hom.left ≫ Spec.algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R) =
      componentOtherIntersectionStructure π i v := Over.w e.hom
  simp only [surfaceIntersectionIsoTwoPoints,Iso.trans_hom,Functor.mapIso_hom,Over.forget_map,
    Category.assoc,he]
  change (pullbackCompMonoIso (otherMap π i v) (i v) (projection π)).hom ≫
    (pullback.snd (otherMap π i v) (i v) ≫ structureMap π i v) = _
  rw [← Category.assoc,pullbackCompMono_snd]

omit [IsLocallyNoetherian Y] [Flat π] [∀ v, IsClosedImmersion (i v)]
  [∀ v, IsIntegral (C v)] [Finite (irreducibleComponents (obj π))] in
theorem surfaceIntersection_finite (v : irreducibleComponents (obj π))
    (e : componentOtherTwoPointIso π i v) : IsFinite (surfaceIntersectionStructure π i v) := by
  rw [← surfaceIntersectionIsoTwoPoints_over π i v e]
  have : IsFinite (Spec.algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) := by
    unfold Spec.algebraMap
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  infer_instance

omit [IsLocallyNoetherian Y] [Flat π] [∀ v, IsClosedImmersion (i v)]
  [∀ v, IsIntegral (C v)] [Finite (irreducibleComponents (obj π))] in
theorem surfaceIntersection_degree (v : irreducibleComponents (obj π))
    (e : componentOtherTwoPointIso π i v) :
    Scheme.Hom.finiteSchemeDegree (IsLocalRing.ResidueField R) (surfaceIntersectionStructure π i
      v) = 2 := by
  rw [finiteSchemeDegree_iso _ _ (surfaceIntersectionIsoTwoPoints π i v e)
    (surfaceIntersectionIsoTwoPoints_over π i v e)]
  exact Scheme.Hom.twoPointSchemeDegree _

variable [IsReduced (obj π)]

include hrange hregular hcartier havoid hunion htensor in
/-- Actual native complementary Cartier ideals multiply to the literal fibre
ideal, by derived Cartierness and reduced whole-fibre coverage. -/
theorem complement_component_product_eq_fibre (v : irreducibleComponents (obj π))
    (e : componentOtherTwoPointIso π i v) :
    (otherSurfaceMap π i v).ker * (surfaceInclusion π i v).ker = (projection π).ker := by
  have hI := otherSurfaceIdeal_invertible π i hrange hregular hcartier havoid hunion htensor v e
  have hJ := surfaceIdeal_invertible π i hrange hregular hcartier v
  rw [hunion Y _ _ (otherSurfaceMap π i v) (surfaceInclusion π i v)
    inferInstance inferInstance hI hJ
    (cartierRestriction_invertible havoid (otherSurfaceMap π i v) (surfaceInclusion π i v) hI
      (surface_not_subset_other π i hrange v))]
  exact (fibreIdeal_eq_inf π i hrange v).symm

/-- The actual tensor product of complementary Cartier ideals is the unit on the ambient scheme.
-/
def complementComponentTensorUnitIso (v : irreducibleComponents (obj π))
    (e : componentOtherTwoPointIso π i v) :
    tensorSheaf Y (idealModule (otherSurfaceMap π i v)) (idealModule (surfaceInclusion π i v)) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  (htensor Y _ _ (otherSurfaceMap π i v) (surfaceInclusion π i v) inferInstance inferInstance
    (otherSurfaceIdeal_invertible π i hrange hregular hcartier havoid hunion htensor v e)
    (surfaceIdeal_invertible π i hrange hregular hcartier v)).choose ≪≫
  eqToIso (congrArg (fun I : Y.IdealSheafData => idealModule I.subschemeι)
    (complement_component_product_eq_fibre π i hrange hregular hcartier havoid hunion htensor v
      e)) ≪≫
  idealImageIso (projection π) ≪≫ (hprincipal R Y π inferInstance).some

include hrange hregular hcartier havoid hunion htensor hprincipal in
theorem complement_component_classes_sum_zero (v : irreducibleComponents (obj π))
    (e : componentOtherTwoPointIso π i v)
    (hJ : IsLocallyRankOne Y (idealModule (surfaceInclusion π i v))) :
    classOf Y ⟨idealModule (otherSurfaceMap π i v),
      otherSurfaceIdeal_invertible π i hrange hregular hcartier havoid hunion htensor v e⟩ +
      classOf Y ⟨idealModule (surfaceInclusion π i v),hJ⟩ = 0 := by
  rw [← classOf_tensor]
  change classOf Y _ = classOf Y (trivialLineBundle Y)
  apply Quotient.sound
  exact ⟨complementComponentTensorUnitIso π i hrange hregular hcartier havoid hunion htensor
    hprincipal v e ≪≫
    (coproductUniqueIso (fun _ : PUnit.{u+1} => SheafOfModules.unit Y.ringCatSheaf)).symm⟩

include hrange hregular hcartier havoid hunion htensor hprincipal hdegree in
/-- Actual two-point intersection forces the actual selected normal degree
minus two. No whole-source cyclic isomorphism, degree, or fibre formula is input. -/
theorem normalDegree_eq_neg_two_of_twoPointIntersection
    (v : irreducibleComponents (obj π)) (e : componentOtherTwoPointIso π i v)
    (hJ : IsLocallyRankOne Y (idealModule (surfaceInclusion π i v))) :
    normalDegree π i q hprod v hJ = -2 := by
  let := component_proper π i q v
  let := component_noetherian π i q v
  let : ∀ d : Scheme.ClosedPoint (C v), IsDiscreteValuationRing ((C v).presheaf.stalk d.val) :=
    component_closedStalk_dvr π i q v
  let := surfaceIntersection_finite π i v e
  rw [normalDegree,selfIntersection_eq_negative_intersectionDegree havoid hdegree
    (otherSurfaceMap π i v) (surfaceInclusion π i v) (structureMap π i v)
    (component_dimension π i q v).le (hprod _ _ _ (component_dimension π i q v))
    (otherSurfaceIdeal_invertible π i hrange hregular hcartier havoid hunion htensor v e) hJ
    (surface_not_subset_other π i hrange v)
    (complement_component_classes_sum_zero π i hrange hregular hcartier havoid hunion htensor
      hprincipal v e hJ)]
  rw [surfaceIntersection_degree π i v e]
  norm_num


end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber

/-- The original no-minus-one argument for an actual comparison whose source components have
actual complementary two-point intersections. All regular-surface and generic-map conditions
remain explicit; the universal contraction premise is not supplied by this theorem. -/
theorem comparison_isIso_of_componentOtherTwoPointIso
    (hcontraction : VerticalContractionExceptionalComponent.{u})
    {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (πX : X ⟶ Spec (.of R)) (πZ : Z ⟶ Spec (.of R))
    (f : X ⟶ Z) [IsProper f] [IsDominant f] (hf : f ≫ πZ = πX)
    (C : irreducibleComponents (obj πX) → Scheme.{u})
    (i : ∀ v, C v ⟶ obj πX)
    [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
    (hrange : ∀ v, Set.range (i v) = v.val)
    (q : ∀ v, Over.mk (ComponentFamily.structureMap πX i v) ≅
      Over.mk (Scheme.ProjectiveLine.structureMap (IsLocalRing.ResidueField R)))
    (endpoints : ∀ v, ComponentFamily.componentOtherTwoPointIso πX i v)
    (hcartier : RegularCodimOneIdealInvertible.{u})
    (havoid : IntegralAvoidanceCartierPullback.{u})
    (hunion : CartierSumIdealEqualsUnion.{u})
    (htensor : CartierIdealTensorProduct.{u})
    (hprincipal : FlatDVRFibreIdealTrivial.{u})
    (hdegree : Scheme.OverField.Curve.Abel.FiniteCartierIdealDegree.{u})
    (hprod : Degree.ProperCurveProductFormula.{u})
    [Flat πX] [IsProper πX] [Flat πZ] [IsProper πZ] [IsReduced (obj πX)]
    (hregularX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hregularZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (hdimX : topologicalKrullDim X = 2) (hdimZ : topologicalKrullDim Z = 2)
    (hfield : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hgeneric : IsIso
      (Scheme.Pullback.GenericRestriction.genericRestriction (F := F) πX πZ f hf)) :
    IsIso f := by
  let : Finite (irreducibleComponents (obj πX)) := components_finite πX
  apply noMinusOne_isIso hcontraction πX πZ f hf C i hrange q hprod
    hregularX hregularZ hdimX hdimZ hfield hgeneric
  intro v hcart
  rw [ComponentFamily.normalDegree_eq_neg_two_of_twoPointIntersection πX i hrange q
    hregularX hcartier havoid hunion htensor hprincipal hdegree hprod v (endpoints v) hcart]
  norm_num

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
