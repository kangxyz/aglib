/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Models.Components.Polygons
public import Aglib.AlgebraicGeometry.Curves.Models.Components.Minimality

/-!
# The conditional actual polygon comparison criterion

Source: frozen R5 `LocalModels/Incidence/CyclicMinimality.lean:62–121`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original component family is unpacked into its actual schemes, inclusions,
range equalities and original-residue-field Over-P¹ isomorphisms. The universal
surface-contraction family remains explicit. Nothing here constructs a model.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.Hom Scheme.Hom.Cartier
open Scheme.OverField.Curve.Picard
universe u

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) (n : ℕ) (e : CyclicFiberIso π n)

/-- The original component selector on the actual irreducible-component subtype. -/
def componentInclusion (v : irreducibleComponents (obj π)) :
    Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R) ⟶ obj π :=
  componentMap π n e ((componentLabelEquiv π n e).symm v)

theorem componentInclusion_closed (hn : 1 < n) (v : irreducibleComponents (obj π)) :
    IsClosedImmersion (componentInclusion π n e v) :=
  componentMap_closed π n e hn _

theorem componentInclusion_range (v : irreducibleComponents (obj π)) :
    Set.range (componentInclusion π n e v) = v.val :=
  (componentLabelEquiv_range π n e _).symm.trans
    (congrArg Subtype.val ((componentLabelEquiv π n e).apply_symm_apply v))

/-- The exact structural triangle uses the original closed component arrow. -/
def componentProjectiveIso (v : irreducibleComponents (obj π)) :
    Over.mk (componentInclusion π n e v ≫ structureMap π) ≅
      Over.mk (Scheme.ProjectiveLine.structureMap (IsLocalRing.ResidueField R)) :=
  Over.isoMk (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 _) (by
    change (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1
      (IsLocalRing.ResidueField R)).hom ≫ Scheme.ProjectiveLine.structureMap
        (IsLocalRing.ResidueField R) =
      componentMap π n e ((componentLabelEquiv π n e).symm v) ≫ structureMap π
    rw [Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over, componentMap_over])

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y] (π : Y ⟶ Spec (.of R)) [Flat π]
  (n : ℕ) (e : CyclicFiberIso π n)

/-- The contraction criterion computes the same genuine normal-bundle degree. -/
theorem cyclicComponents_normalDegree_eq
    (hcartier : RegularCodimOneIdealInvertible.{u})
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (hprod : Degree.ProperCurveProductFormula.{u}) (hn : 1 < n)
    (v : irreducibleComponents (obj π))
    (hcart : IsLocallyRankOne Y
      (idealModule (ComponentFamily.surfaceInclusion π (componentInclusion π n e) v))) :
    ComponentFamily.normalDegree π (componentInclusion π n e) (componentProjectiveIso π n e)
      hprod v hcart =
      componentSelfIntersection π n e hcartier hregular hprod hn
        ((componentLabelEquiv π n e).symm v) := by
  unfold ComponentFamily.normalDegree componentSelfIntersection
  simp only [ComponentFamily.structureMap, ComponentFamily.surfaceInclusion,
    componentInclusion, componentMap_over]

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.PolygonComponents
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
open PolygonComponents

/-- Every actual comparison map satisfying the original surface conditions is
an isomorphism when the source has a literal polygon fibre of length greater
than one and the original contraction and Cartier families are supplied. -/
theorem cyclic_comparison_isIso
    (hcontraction : VerticalContractionExceptionalComponent.{u})
    {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] [IsNoetherian X] [IsNoetherian Z]
    (πX : X ⟶ Spec (.of R)) (πZ : Z ⟶ Spec (.of R))
    (f : X ⟶ Z) [IsProper f] [IsDominant f] (hf : f ≫ πZ = πX)
    (n : ℕ) (e : CyclicFiberIso πX n) (hn : 1 < n)
    (hcartier : RegularCodimOneIdealInvertible.{u})
    (havoid : IntegralAvoidanceCartierPullback.{u})
    (hunion : CartierSumIdealEqualsUnion.{u})
    (htensor : CartierIdealTensorProduct.{u})
    (hprincipal : FlatDVRFibreIdealTrivial.{u})
    (hdegree : Scheme.OverField.Curve.Abel.FiniteCartierIdealDegree.{u})
    (hprod : Degree.ProperCurveProductFormula.{u})
    [Flat πX] [IsProper πX] [Flat πZ] [IsProper πZ]
    (hregularX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hregularZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (hdimX : topologicalKrullDim X = 2) (hdimZ : topologicalKrullDim Z = 2)
    (hfield : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hgeneric : IsIso
      (Scheme.Pullback.GenericRestriction.genericRestriction (F := F) πX πZ f hf)) :
    IsIso f := by
  let : ∀ v : irreducibleComponents (obj πX),
      IsClosedImmersion (componentInclusion πX n e v) := componentInclusion_closed πX n e hn
  apply noMinusOne_isIso hcontraction πX πZ f hf
    (fun _ => Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R))
    (componentInclusion πX n e) (componentInclusion_range πX n e)
    (componentProjectiveIso πX n e) hprod hregularX hregularZ hdimX hdimZ hfield hgeneric
  intro v hcart
  rw [cyclicComponents_normalDegree_eq πX n e hcartier hregularX hprod hn v hcart,
    componentSelfIntersection_eq_neg_two πX n e hcartier hregularX havoid hunion htensor
      hprincipal hdegree hprod hn]
  norm_num

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
