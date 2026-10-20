module

import Aglib.AlgebraicGeometry.Curves.Models.Components.CyclicMinimality

/-! Public clients for literal residue fibres and their actual component geometry. -/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open Scheme.LocalRing Scheme.LocalRing.ResidueFiber
open Scheme.Modules.Invertible Scheme.Hom Scheme.Hom.Cartier
universe u

namespace AglibTest.SurfaceComponents

example {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) :
    obj π = pullback π (residueSpecMap R) := rfl

example {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))
    (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ π = 𝟙 _) :
    ResidueFiber.«section» π σ hσ ≫ projection π = residueSpecMap R ≫ σ :=
  section_projection π σ hσ

example {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))
    (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ π = 𝟙 _) :
    ResidueFiber.«section» π σ hσ ≫ structureMap π = 𝟙 _ :=
  section_structureMap π σ hσ

example {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (π : Y ⟶ Spec (.of R)) [Flat π]
    {C : Scheme.{u}} [IsIntegral C] (i : C ⟶ obj π) [IsClosedImmersion i]
    (hi : Set.range i ∈ irreducibleComponents (obj π)) (c : C) :
    (RingHom.ker ((i ≫ projection π).stalkMap c).hom).height = 1 :=
  component_stalkKernel_height_one π i hi c

example {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) (e : OneGonIso π) :
    ¬ Nonempty (obj π ≅ Scheme.ProjectiveLine.projectiveP1 (IsLocalRing.ResidueField R)) :=
  oneGon_not_isoP1 π e

example {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) (e : TwoGonIso π) :
    Over.mk (twoGonSurfaceIntersectionStructure π e) ≅
      Over.mk (Spec.algebraMap (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField R × IsLocalRing.ResidueField R)) :=
  twoGonSurfaceIntersectionOverIsoTwoPoints π e

example {R : Type u} [CommRing R] [IsLocalRing R]
    {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R)) (e : CyclicFiberIso π 1) : OneGonIso π :=
  cyclicOneGonIso π e

example {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (π : Y ⟶ Spec (.of R)) [Flat π]
    (n : ℕ) (e : CyclicFiberIso π n) (hn : 1 < n)
    (hcartier : RegularCodimOneIdealInvertible.{u})
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (havoid : IntegralAvoidanceCartierPullback.{u})
    (hunion : CartierSumIdealEqualsUnion.{u})
    (htensor : CartierIdealTensorProduct.{u})
    (hprincipal : FlatDVRFibreIdealTrivial.{u})
    (hdegree : Scheme.OverField.Curve.Abel.FiniteCartierIdealDegree.{u})
    (hprod : Scheme.OverField.Curve.Picard.Degree.ProperCurveProductFormula.{u})
    (i : Fin n) :
    PolygonComponents.componentSelfIntersection π n e hcartier hregular hprod hn i = -2 :=
  PolygonComponents.componentSelfIntersection_eq_neg_two π n e hcartier hregular havoid
    hunion htensor hprincipal hdegree hprod hn i

end AglibTest.SurfaceComponents
