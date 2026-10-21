/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Models.Components.TwoGon
public import Aglib.AlgebraicGeometry.Curves.Models.Components.CartierUnions
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.Intersections
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.One
public import Aglib.AlgebraicGeometry.Limits.PullbackTransport

/-!
# Actual indexed polygon components, intersections and normal degrees

Source: frozen R5 `LocalModels/Incidence/Polygons.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original actual schemes, kernel ideals and structural triangles are retained.
Unused model wrappers are replaced by the actual scheme and map parameters.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry Polynomial
open Scheme.Modules.Invertible Scheme.Modules Scheme.Hom Scheme.Hom.Cartier
open Scheme.IdealSheafData Scheme.PinchedLine Scheme.Polygon
open Scheme.Hom.ActualSpecialFiber (pullbackCompMonoIso)
open Scheme.Hom.ActualLocalModel.CyclicComponents (pullbackCompMonoIso_hom_snd_assoc)
open scoped Polynomial
universe u
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))

/-- A literal isomorphism of the entire actual residue fibre, over its original field. -/
abbrev CyclicFiberIso (n : ℕ) := Over.mk (structureMap π) ≅
  Over.mk (Scheme.Polygon.structureMap (IsLocalRing.ResidueField R) n)

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
namespace AlgebraicGeometry.Scheme.PinchedLine

/-- The stalk at a closed point of the glued projective line is a discrete valuation ring. -/
instance closedPoint_dvr (k : Type u) [Field k]
    (d : Scheme.ClosedPoint (lineGluing k)) :
    IsDiscreteValuationRing ((lineGluing k).presheaf.stalk d.val) :=
  line_closedStalk_dvr k d.val d.property

end AlgebraicGeometry.Scheme.PinchedLine
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) (n : ℕ) (e : CyclicFiberIso π n)

/-- The actual component of the literal special fibre, through the whole-fibre
classification isomorphism. Its source is the constructed genuine P1. -/
def componentMap (i : Fin n) : Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R) ⟶
    (obj π) :=
  componentTarget (IsLocalRing.ResidueField R) n i ≫ e.inv.left

/-- The polygon complement mapped into the actual residue fibre through the whole-fibre
isomorphism. -/
def complementMap (i : Fin n) : otherGlobalScheme (IsLocalRing.ResidueField R) n i ⟶ (obj π) :=
  otherGlobalInclusion (IsLocalRing.ResidueField R) n i ≫ e.inv.left

/-- The parametrized polygon component mapped into the ambient scheme. -/
abbrev componentSurfaceMap (i : Fin n) : Scheme.PinchedLine.lineGluing
    (IsLocalRing.ResidueField R) ⟶ Y :=
  componentMap π n e i ≫ (projection π)
/-- The polygon complement mapped into the ambient scheme. -/
abbrev complementSurfaceMap (i : Fin n) : otherGlobalScheme (IsLocalRing.ResidueField R) n i ⟶ Y :=
  complementMap π n e i ≫ (projection π)

theorem componentMap_closed (hn : 1 < n) (i : Fin n) : IsClosedImmersion (componentMap π n e i)
    := by
  let := componentTarget_closedImmersion_of_one_lt (IsLocalRing.ResidueField R) n hn i
  unfold componentMap
  infer_instance

/-- The transported polygon complement is a closed subscheme of the actual residue fibre. -/
instance complementMap_closed (i : Fin n) : IsClosedImmersion (complementMap π n e i) := by
  unfold complementMap
  infer_instance

@[reassoc (attr := simp)] theorem componentMap_over (i : Fin n) :
    componentMap π n e i ≫ (structureMap π) = Scheme.PinchedLine.lineStructure
        (IsLocalRing.ResidueField R) := by
  have h : e.inv.left ≫ (structureMap π) = Scheme.Polygon.structureMap
      (IsLocalRing.ResidueField R) n := Over.w e.inv
  rw [componentMap, Category.assoc, h, componentTarget_over]

/-- Each component has the correct actual maximal-irreducible image in π's fibre. -/
theorem componentMap_range_irreducible (i : Fin n) :
    Set.range (componentMap π n e i) ∈ irreducibleComponents (obj π) := by
  change Set.range (e.inv.left ∘ componentTarget (IsLocalRing.ResidueField R) n i) ∈ _
  rw [Set.range_comp, componentTarget_range]
  apply image_mem_irreducibleComponents_of_isPreirreducible_fiber
    e.inv.left e.inv.left.continuous e.inv.left.homeomorph.isOpenMap
    (fun _ => (Set.subsingleton_singleton.preimage
        e.inv.left.homeomorph.injective).isPreirreducible)
    e.inv.left.homeomorph.surjective
  change targetComponent (IsLocalRing.ResidueField R) n i ∈
    irreducibleComponents (cycleScheme (IsLocalRing.ResidueField R) n)
  rw [targetComponent_inventory]
  exact ⟨i,rfl⟩

/-- The actual complement does not contain the selected component. -/
theorem componentSurface_not_subset_complement (i : Fin n) :
    ¬ Set.range (componentSurfaceMap π n e i) ⊆ Set.range (complementSurfaceMap π n e i) := by
  intro h
  apply componentTarget_not_subset_other (IsLocalRing.ResidueField R) n i
  rintro _ ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := h ⟨x,rfl⟩
  exact ⟨y,e.inv.left.homeomorph.injective ((projection π).isClosedEmbedding.injective hy)⟩

/-- Distinct actual surface component images are pairwise noncontained. -/
theorem componentSurface_pairwise_not_subset :
    Pairwise (fun i j : Fin n =>
      ¬ Set.range (componentSurfaceMap π n e i) ⊆ Set.range (componentSurfaceMap π n e j)) := by
  intro i j hij h
  apply hij
  apply targetComponent_subset_index (IsLocalRing.ResidueField R) n i j
  rw [← componentTarget_range, ← componentTarget_range]
  rintro _ ⟨x,rfl⟩
  obtain ⟨y,hy⟩ := h ⟨x,rfl⟩
  exact ⟨y,e.inv.left.homeomorph.injective ((projection π).isClosedEmbedding.injective hy)⟩

/-- The actual component and its actual complement exhaust the reduced fibre. -/
theorem surface_ranges_cover (i : Fin n) :
    Set.range (componentSurfaceMap π n e i) ∪ Set.range (complementSurfaceMap π n e i) =
      Set.range (projection π) := by
  change Set.range (((projection π) ∘ e.inv.left) ∘ componentTarget _ n i) ∪
    Set.range (((projection π) ∘ e.inv.left) ∘ otherGlobalInclusion _ n i) = _
  rw [Set.range_comp, Set.range_comp, ← Set.image_union, component_and_others_cover, Set.image_univ]
  have hs : Function.Surjective e.inv.left := e.inv.left.homeomorph.surjective
  rw [Set.range_comp, hs.range_eq, Set.image_univ]

include n e in
theorem specialFiber_reduced : IsReduced (obj π) := by
  let : IsReduced (Over.mk (Scheme.Polygon.structureMap
      (IsLocalRing.ResidueField R) n)).left :=
    cycleScheme_reduced_from_charts (IsLocalRing.ResidueField R) n
  exact isReduced_of_isOpenImmersion e.hom.left

/-- Scheme-theoretic union equals the literal fibre, by actual reducedness
and the proved coverage, independently of Cartier multiplication. -/
theorem fibreIdeal_eq_inf (hn : 1 < n) (i : Fin n) :
    (projection π).ker =
      (complementSurfaceMap π n e i).ker ⊓ (componentSurfaceMap π n e i).ker := by
  let := componentMap_closed π n e hn i
  let := specialFiber_reduced π n e
  exact reduced_closed_union_ideal (projection π) (complementSurfaceMap π n e i)
    (componentSurfaceMap π n e i) (by rw [Set.union_comm]; exact surface_ranges_cover π n e i)

/-- The intersection of a polygon component and its complement in the ambient scheme. -/
abbrev surfaceIntersection (i : Fin n) : Scheme.{u} :=
  pullback (complementSurfaceMap π n e i) (componentSurfaceMap π n e i)
/-- The residue-field structure map of the ambient component-complement intersection. -/
abbrev surfaceIntersectionStructure (i : Fin n) : surfaceIntersection π n e i ⟶ Spec (.of
    (IsLocalRing.ResidueField R)) :=
  pullback.snd _ _ ≫ Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R)

/-- The degree-two intersection is transported to the actual ambient model,
with the same two components and their exact structural maps. -/
def surfaceIntersectionIsoTwoPoints (hn : 1 < n) (i : Fin n) :
    surfaceIntersection π n e i ≅
      Spec (.of (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) :=
  pullbackCompMonoIso (complementMap π n e i) (componentMap π n e i) (projection π) ≪≫
    pullbackCompMonoIso (otherGlobalInclusion (IsLocalRing.ResidueField R) n i)
      (componentTarget (IsLocalRing.ResidueField R) n i) e.inv.left ≪≫
    pullbackSymmetry (otherGlobalInclusion (IsLocalRing.ResidueField R) n i)
      (componentTarget (IsLocalRing.ResidueField R) n i) ≪≫
    globalComponentComplementIsoTwoPoints (IsLocalRing.ResidueField R) n hn i

@[reassoc] theorem surfaceIntersectionIsoTwoPoints_over (hn : 1 < n) (i : Fin n) :
    (surfaceIntersectionIsoTwoPoints π n e hn i).hom ≫
      Spec.algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R) =
      surfaceIntersectionStructure π n e i := by
  simp only [surfaceIntersectionIsoTwoPoints, Iso.trans_hom, Category.assoc,
    globalComponentComplementIsoTwoPoints_over, globalComplementFirst,
    pullbackSymmetry_hom_comp_fst_assoc, pullbackCompMonoIso_hom_snd_assoc]
  exact pullbackCompMonoIso_hom_snd_assoc (complementMap π n e i) (componentMap π n e i)
    (projection π) (Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R))

theorem surfaceIntersection_degree (hn : 1 < n) (i : Fin n) :
    Scheme.Hom.finiteSchemeDegree (IsLocalRing.ResidueField R) (surfaceIntersectionStructure π
        n e i) = 2 := by
  rw [finiteSchemeDegree_iso _ _ (surfaceIntersectionIsoTwoPoints π n e hn i)
    (surfaceIntersectionIsoTwoPoints_over π n e hn i)]
  exact Scheme.Hom.twoPointSchemeDegree _

theorem surfaceIntersection_finite (hn : 1 < n) (i : Fin n) :
    IsFinite (surfaceIntersectionStructure π n e i) := by
  rw [← surfaceIntersectionIsoTwoPoints_over π n e hn i]
  have : IsFinite (Spec.algebraMap (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) := by
    unfold Spec.algebraMap
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  infer_instance

theorem surfaceIntersection_reduced (hn : 1 < n) (i : Fin n) :
    IsReduced (surfaceIntersection π n e i) :=
  isReduced_of_isOpenImmersion (surfaceIntersectionIsoTwoPoints π n e hn i).hom

/-- Exact finite-inf surface complement ideal needed by Cartier-union induction. -/
theorem complementSurface_kernel (i : Fin n) :
    (complementSurfaceMap π n e i).ker =
      ⨅ j : {j : Fin n // j ≠ i}, (componentSurfaceMap π n e j.val).ker := by
  change (otherGlobalInclusion (IsLocalRing.ResidueField R) n i ≫
    (e.inv.left ≫ (projection π))).ker = _
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, otherGlobalIdeal_eq_iInf,
    (Scheme.IdealSheafData.map_gc (e.inv.left ≫ (projection π))).u_iInf]
  simp only [Scheme.IdealSheafData.map_ker]
  rfl

/-- The original actual line-degree applicability, from the given proper-curve family. -/
theorem component_productFormula (hprod :
    Scheme.OverField.Curve.Picard.Degree.ProperCurveProductFormula.{u}) :
    Scheme.OverField.Curve.Picard.Degree.PrincipalProductFormula
      (Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R))
      (Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R)) :=
  hprod _ _ _ (line_dimension_eq_one _)

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y] (π : Y ⟶ Spec (.of R)) [Flat π]
  (n : ℕ) (e : CyclicFiberIso π n)

/-- Genuine component ideal invertibility from the two accepted universal
codimension-one families, with applicability proved on this model. -/
theorem componentSurface_ideal_invertible (hcartier : RegularCodimOneIdealInvertible.{u})
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) (hn : 1 < n) (i : Fin n) :
    IsLocallyRankOne Y (idealModule (componentSurfaceMap π n e i)) := by
  let := componentMap_closed π n e hn i
  exact component_ideal_invertible π hcartier hregular (componentMap π n e i)
    (componentMap_range_irreducible π n e i)

variable (hcartier : RegularCodimOneIdealInvertible.{u})
  (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
  (havoid : IntegralAvoidanceCartierPullback.{u})
  (hunion : CartierSumIdealEqualsUnion.{u})
  (htensor : CartierIdealTensorProduct.{u})
  (hprincipal : FlatDVRFibreIdealTrivial.{u})
  (hdegree : Scheme.OverField.Curve.Abel.FiniteCartierIdealDegree.{u})
  (hprod : Scheme.OverField.Curve.Picard.Degree.ProperCurveProductFormula.{u}) (hn : 1 < n)

include hcartier hregular havoid hunion htensor hn in
/-- The reduced complement is Cartier by native finite-union induction.
Its nonempty index set follows from n>1 and the actual cyclic successor. -/
theorem complementSurface_ideal_invertible (i : Fin n) :
    IsLocallyRankOne Y (idealModule (complementSurfaceMap π n e i)) := by
  classical
  let : Nonempty {j : Fin n // j ≠ i} :=
    ⟨⟨finRotate n i, Fin.finRotate_ne_self_of_one_lt n hn i⟩⟩
  let (j : {j : Fin n // j ≠ i}) : IsClosedImmersion (componentSurfaceMap π n e j.val) := by
    let := componentMap_closed π n e hn j.val
    exact inferInstanceAs (IsClosedImmersion (componentMap π n e j.val ≫ (projection π)))
  have hc := iInfIdeal_cartier (fun j : {j : Fin n // j ≠ i} => componentSurfaceMap π n e j.val)
    havoid hunion htensor (fun j => componentSurface_ideal_invertible π n e hcartier hregular
        hn j.val)
    (fun a b hab => componentSurface_pairwise_not_subset π n e
      (show a.val ≠ b.val from fun h => hab (Subtype.ext h)))
  rw [← complementSurface_kernel π n e i] at hc
  exact isLocallyRankOne_of_iso Y (idealImageIso (complementSurfaceMap π n e i)) hc

/-- The integer is the degree of the dual actual component ideal restricted
to that component. It is not assigned the intended value. -/
def componentSelfIntersection (i : Fin n) : ℤ :=
  actualSelfIntersection (componentSurfaceMap π n e i)
    (Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R))
    (line_dimension_eq_one _).le (component_productFormula (R := R) hprod)
    (componentSurface_ideal_invertible π n e hcartier hregular hn i)

include hcartier hregular havoid hunion hn in
/-- The two actual Cartier divisors add scheme-theoretically to the literal
reduced fibre. The complement's Cartierness is an internal finite-union input. -/
theorem complement_component_product_eq_fibre (i : Fin n)
    (hcomp : IsLocallyRankOne Y (idealModule (complementSurfaceMap π n e i))) :
    (complementSurfaceMap π n e i).ker * (componentSurfaceMap π n e i).ker =
      (projection π).ker := by
  let := componentMap_closed π n e hn i
  rw [hunion Y _ _ (complementSurfaceMap π n e i) (componentSurfaceMap π n e i)
    inferInstance inferInstance hcomp (componentSurface_ideal_invertible π n e hcartier
        hregular hn i)
    (cartierRestriction_invertible havoid (complementSurfaceMap π n e i)
      (componentSurfaceMap π n e i) hcomp (componentSurface_not_subset_complement π n e i))]
  exact (fibreIdeal_eq_inf π n e hn i).symm

/-- The native tensor multiplication comparison and uniformizer trivialization
produce the actual tensor-unit isomorphism. -/
def complementComponentTensorUnitIso (i : Fin n)
    (hcomp : IsLocallyRankOne Y (idealModule (complementSurfaceMap π n e i))) :
    tensorSheaf Y (idealModule (complementSurfaceMap π n e i))
      (idealModule (componentSurfaceMap π n e i)) ≅ SheafOfModules.unit Y.ringCatSheaf := by
  let := componentMap_closed π n e hn i
  exact (htensor Y _ _ (complementSurfaceMap π n e i) (componentSurfaceMap π n e i)
    inferInstance inferInstance hcomp (componentSurface_ideal_invertible π n e hcartier
        hregular hn i)).choose ≪≫
    eqToIso (congrArg (fun I : Y.IdealSheafData => idealModule I.subschemeι)
      (complement_component_product_eq_fibre π n e hcartier hregular havoid hunion hn i hcomp)) ≪≫
    idealImageIso (projection π) ≪≫ (hprincipal R Y π (inferInstance : Flat π)).some

include havoid hunion htensor hprincipal in
/-- Picard cancellation is proved from the actual kernel tensor product. -/
theorem complement_component_classes_sum_zero (i : Fin n)
    (hcomp : IsLocallyRankOne Y (idealModule (complementSurfaceMap π n e i))) :
    classOf Y ⟨idealModule (complementSurfaceMap π n e i),hcomp⟩ +
      classOf Y ⟨idealModule (componentSurfaceMap π n e i),
        componentSurface_ideal_invertible π n e hcartier hregular hn i⟩ = 0 := by
  rw [← classOf_tensor]
  change classOf Y _ = classOf Y (trivialLineBundle Y)
  apply Quotient.sound
  exact ⟨complementComponentTensorUnitIso π n e hcartier hregular havoid hunion htensor
      hprincipal hn i hcomp ≪≫
    (coproductUniqueIso (fun _ : PUnit.{u+1} => SheafOfModules.unit Y.ringCatSheaf)).symm⟩

include havoid hunion htensor hprincipal hdegree in
/-- Once native finite-union Cartierness is applied, the selected component's
self-intersection is forced to be -2 by its actual two-point intersection. -/
theorem componentSelfIntersection_eq_neg_two_of_complement_cartier (i : Fin n)
    (hcomp : IsLocallyRankOne Y (idealModule (complementSurfaceMap π n e i))) :
    componentSelfIntersection π n e hcartier hregular hprod hn i = -2 := by
  let := componentMap_closed π n e hn i
  let := surfaceIntersection_finite π n e hn i
  rw [componentSelfIntersection,
    selfIntersection_eq_negative_intersectionDegree havoid hdegree
      (complementSurfaceMap π n e i) (componentSurfaceMap π n e i)
      (Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R))
      (line_dimension_eq_one _).le (component_productFormula (R := R) hprod) hcomp
      (componentSurface_ideal_invertible π n e hcartier hregular hn i)
      (componentSurface_not_subset_complement π n e i)
      (complement_component_classes_sum_zero π n e hcartier hregular havoid hunion htensor
          hprincipal hn i hcomp)]
  rw [surfaceIntersection_degree π n e hn i]
  norm_num

include havoid hunion htensor hprincipal hdegree in
/-- General-n genuine normal-bundle self-intersection. No component count,
intersection degree, complement Cartierness or fibre formula is supplied. -/
theorem componentSelfIntersection_eq_neg_two (i : Fin n) :
    componentSelfIntersection π n e hcartier hregular hprod hn i = -2 :=
  componentSelfIntersection_eq_neg_two_of_complement_cartier π n e hcartier hregular havoid hunion
    htensor hprincipal hdegree hprod hn i
    (complementSurface_ideal_invertible π n e hcartier hregular havoid hunion htensor hn i)

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- Actual normalized source points above the intersection with other components. -/
def componentOtherBranches (i : Fin n) : Set (normalizedScheme k n) :=
  {z | z ∈ Set.range (componentLine k n i) ∧
    gluedPolynomialCover k n z ∈ Set.range (otherGlobalInclusion k n i)}

/-- Every conductor endpoint lies on a genuinely different component for n>1;
conversely any intersection with another component lies at the actual node locus. -/
theorem componentOtherBranches_eq_boundary (hn : 1 < n) (i : Fin n) :
    componentOtherBranches k n i = componentBoundaryBranches k n i := by
  ext z
  constructor
  · rintro ⟨hz,ho⟩
    refine ⟨hz,?_⟩
    rw [otherGlobalInclusion_range] at ho
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ho
    exact targetComponent_inter_subset_nodes k n i j.val (Ne.symm j.property)
      ⟨⟨z,hz,rfl⟩,hj⟩
  · intro hz
    have hc := hz.1
    rw [componentBoundaryBranches_eq] at hz
    refine ⟨hc,?_⟩
    rw [otherGlobalInclusion_range]
    rcases hz with rfl | rfl
    · refine Set.mem_iUnion.mpr ⟨⟨(finRotate n).symm i,Fin.finRotate_symm_ne_self_of_one_lt n
        hn i⟩,?_⟩
      have he := gluedBranch_zero_map k n ((finRotate n).symm i)
      simp only [Equiv.apply_symm_apply] at he
      rw [he]
      exact (gluedNodePoint_on_component_iff k n _ _).mpr (Or.inl rfl)
    · refine Set.mem_iUnion.mpr ⟨⟨finRotate n i,Fin.finRotate_ne_self_of_one_lt n hn i⟩,?_⟩
      rw [gluedBranch_one_map]
      exact (gluedNodePoint_on_component_iff k n _ _).mpr (Or.inr rfl)

theorem componentOtherBranches_card (hn : 1 < n) (i : Fin n) :
    (componentOtherBranches k n i).ncard = 2 := by
  rw [componentOtherBranches_eq_boundary k n hn i, componentBoundaryBranches_card]

end AlgebraicGeometry.Scheme.Polygon
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) (n : ℕ) (e : CyclicFiberIso π n)

/-- Labels are identified bijectively with the actual irreducible components
of the actual model fibre, using the already proved literal cyclic inventory. -/
def componentLabelEquiv : Fin n ≃ irreducibleComponents (obj π) :=
  (componentEquiv (IsLocalRing.ResidueField R) n).trans
    (componentsEquiv (((Over.forget _).mapIso e).symm))

@[simp] theorem componentLabelEquiv_range (i : Fin n) :
    (componentLabelEquiv π n e i).val = Set.range (componentMap π n e i) := by
  change e.inv.left '' targetComponent (IsLocalRing.ResidueField R) n i =
    Set.range (e.inv.left ∘ componentTarget (IsLocalRing.ResidueField R) n i)
  rw [Set.range_comp, componentTarget_range]

include e in
theorem components_card : Nat.card (irreducibleComponents (obj π)) = n := by
  rw [← Nat.card_congr (componentLabelEquiv π n e)]
  simp

include e in
/-- Actual smooth-rational geometry on each actual fibre component. -/
theorem component_smoothRational (hn : 1 < n) (v : irreducibleComponents (obj π)) :
    actualSmoothRationalComponent π v.val := by
  let i := (componentLabelEquiv π n e).symm v
  refine ⟨Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R), componentMap π n e i,
    componentMap_closed π n e hn i, ?_, ?_, ?_⟩
  · exact (componentLabelEquiv_range π n e i).symm.trans
      (congrArg Subtype.val ((componentLabelEquiv π n e).apply_symm_apply v))
  · rw [componentMap_over]
    infer_instance
  · refine ⟨Over.isoMk (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 _) ?_⟩
    change (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 (IsLocalRing.ResidueField R)).hom ≫
      Scheme.ProjectiveLine.structureMap (IsLocalRing.ResidueField R) =
      componentMap π n e i ≫ (structureMap π)
    rw [Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over, componentMap_over]

/-- The actual normalized-source map into the actual model special fibre. -/
def normalizationMap : normalizedScheme (IsLocalRing.ResidueField R) n ⟶ (obj π) :=
  gluedPolynomialCover (IsLocalRing.ResidueField R) n ≫ e.inv.left

/-- The normalization branches lying over the complement of the actual component indexed by `v`. -/
def actualOtherBranches (v : irreducibleComponents (obj π)) :
    Set (normalizedScheme (IsLocalRing.ResidueField R) n) :=
  componentOtherBranches (IsLocalRing.ResidueField R) n ((componentLabelEquiv π n e).symm v)

/-- Branch membership uses the actual complement in the same fibre. -/
theorem actualOtherBranches_iff (v : irreducibleComponents (obj π))
    (z : normalizedScheme (IsLocalRing.ResidueField R) n) :
    z ∈ actualOtherBranches π n e v ↔
      z ∈ Set.range (componentLine (IsLocalRing.ResidueField R) n ((componentLabelEquiv π n
          e).symm v)) ∧
      normalizationMap π n e z ∈ Set.range (complementMap π n e ((componentLabelEquiv π n
          e).symm v)) := by
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y,congrArg e.inv.left hy⟩
  · rintro ⟨y,hy⟩
    exact ⟨y,e.inv.left.homeomorph.injective hy⟩

theorem actualOtherBranches_card (hn : 1 < n) (v : irreducibleComponents (obj π)) :
    (actualOtherBranches π n e v).ncard = 2 :=
  componentOtherBranches_card (IsLocalRing.ResidueField R) n hn _

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k]

/-- The unique-index overlap has its original constant/evaluation ring inverse. -/
instance overlapMap_one_isIso : IsIso (overlapMap k 1) := by
  apply isIso_SpecMap_iff.mpr
  constructor
  · intro a b h
    exact congrArg (fun f : Fin 1 → W k => f 0) h
  · intro p
    refine ⟨p 0, ?_⟩
    funext i
    change p 0 = p i
    rw [Subsingleton.elim i 0]

end AlgebraicGeometry.Scheme.Polygon
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))

/-- Literal whole-fibre transport through the original one-cycle comparison. -/
def cyclicOneGonIso (e : CyclicFiberIso π 1) : OneGonIso π :=
  e ≪≫ Scheme.Polygon.cycleOneOverIso (IsLocalRing.ResidueField R)

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
