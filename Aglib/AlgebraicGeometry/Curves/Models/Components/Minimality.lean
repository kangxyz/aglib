/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Aglib.AlgebraicGeometry.Curves.Models.Components.NormalDegree
public import Aglib.AlgebraicGeometry.Curves.Nodal.LineGeometry
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedClosedUnion
public import Aglib.AlgebraicGeometry.Limits.GenericRestriction
public import Aglib.AlgebraicGeometry.FunctionField.Map

/-!
# Actual component families and the conditional no-minus-one criterion

Source: frozen R5 `LocalModels/Incidence/Minimality.lean:319–413,435–480`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
The original component schemes, inclusions, ranges and Over-P¹ isomorphisms
are separate actual arguments. No model or component-presentation record is used.
The original universal surface-contraction family remains an explicit condition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules.Invertible Scheme.Hom Scheme.IdealSheafData
open Scheme.OverField.Curve.Picard
universe u

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))
  {C : irreducibleComponents (obj π) → Scheme.{u}}
  (i : ∀ v, C v ⟶ obj π)

/-- Coverage follows from the exact index by all actual irreducible components. -/
theorem exhaustive (hrange : ∀ v, Set.range (i v) = v.val) (x : obj π) :
    ∃ v, x ∈ Set.range (i v) := by
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  rw [hrange]
  exact mem_irreducibleComponent

/-- The actual integral closed component is determined by its vanishing ideal. -/
theorem kernel_eq_componentVanishingIdeal
    [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
    (hrange : ∀ v, Set.range (i v) = v.val) (v : irreducibleComponents (obj π)) :
    (i v).ker = vanishingIdeal ⟨v.val, isClosed_of_mem_irreducibleComponents _ v.property⟩ := by
  rw [kernel_eq_vanishingIdeal]
  congr 1
  ext x
  simp only [Scheme.Hom.support_ker, hrange]
  change x ∈ closure v.val ↔ x ∈ v.val
  rw [(isClosed_of_mem_irreducibleComponents _ v.property).closure_eq]

/-- The residue-field structure map of the component indexed by `v`. -/
abbrev structureMap (v : irreducibleComponents (obj π)) :=
  i v ≫ ResidueFiber.structureMap π
/-- The inclusion of the component indexed by `v` into the ambient scheme. -/
abbrev surfaceInclusion (v : irreducibleComponents (obj π)) :=
  i v ≫ projection π

variable (q : ∀ v, Over.mk (structureMap π i v) ≅
  Over.mk (Scheme.ProjectiveLine.structureMap (IsLocalRing.ResidueField R)))

/-- The component identified with the glued projective line using the supplied Over-isomorphism
`q`. -/
def lineIso (v : irreducibleComponents (obj π)) :
    C v ≅ Scheme.PinchedLine.lineGluing (IsLocalRing.ResidueField R) :=
  ((Over.forget _).mapIso (q v)) ≪≫
    (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 _).symm

@[reassoc] theorem lineIso_over (v : irreducibleComponents (obj π)) :
    (lineIso π i q v).hom ≫ Scheme.PinchedLine.lineStructure (IsLocalRing.ResidueField R) =
      structureMap π i v := by
  simp only [lineIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.forget_map,
    Category.assoc]
  rw [← Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over, Iso.inv_hom_id_assoc]
  exact Over.w (q v).hom

include i q

theorem component_proper (v : irreducibleComponents (obj π)) :
    IsProper (structureMap π i v) := by
  rw [← lineIso_over π i q v]
  infer_instance

theorem component_finiteType (v : irreducibleComponents (obj π)) :
    LocallyOfFiniteType (structureMap π i v) := by
  let := component_proper π i q v
  infer_instance

theorem component_noetherian (v : irreducibleComponents (obj π)) : IsNoetherian (C v) := by
  let := component_proper π i q v
  let : IsLocallyNoetherian (C v) := LocallyOfFiniteType.isLocallyNoetherian (structureMap π i v)
  let : CompactSpace (C v) := QuasiCompact.compactSpace_of_compactSpace (structureMap π i v)
  exact ⟨⟩

theorem component_closedStalk_dvr [∀ v, IsIntegral (C v)]
    (v : irreducibleComponents (obj π)) (d : Scheme.ClosedPoint (C v)) :
    IsDiscreteValuationRing ((C v).presheaf.stalk d.val) :=
  Scheme.PinchedLine.closedStalk_dvr_of_isoLine (lineIso π i q v) d.val d.property

theorem component_dimension (v : irreducibleComponents (obj π)) :
    topologicalKrullDim (C v) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (lineIso π i q v).hom.homeomorph.isHomeomorph).trans
      (Scheme.PinchedLine.line_dimension_eq_one _)

/-- The degree is computed from the actual restricted dual kernel ideal. -/
def normalDegree [∀ v, IsIntegral (C v)]
    (hprod : Degree.ProperCurveProductFormula.{u})
    (v : irreducibleComponents (obj π))
    (hcart : IsLocallyRankOne Y (idealModule (surfaceInclusion π i v))) : ℤ := by
  let := component_proper π i q v
  let := component_noetherian π i q v
  let : ∀ d : Scheme.ClosedPoint (C v),
      IsDiscreteValuationRing ((C v).presheaf.stalk d.val) :=
    component_closedStalk_dvr π i q v
  exact actualSelfIntersection (surfaceInclusion π i v) (structureMap π i v)
    (component_dimension π i q v).le (hprod _ _ _ (component_dimension π i q v)) hcart

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
open ComponentFamily

/-- The original unsupplied universal exceptional-component family, on actual maps.
Regularity, dimensions, both generic isomorphisms and the full original component
family remain explicit. This definition is not a proof of surface factorization. -/
def VerticalContractionExceptionalComponent : Prop :=
  ∀ (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (X Z : Scheme.{u}) [IsIntegral X] [IsIntegral Z]
    [IsNoetherian X] [IsNoetherian Z]
    (πX : X ⟶ Spec (.of R)) (πZ : Z ⟶ Spec (.of R))
    (f : X ⟶ Z) [IsProper f] [IsDominant f] (hf : f ≫ πZ = πX)
    (C : irreducibleComponents (obj πX) → Scheme.{u})
    (i : ∀ v, C v ⟶ obj πX)
    [∀ v, IsClosedImmersion (i v)] [∀ v, IsIntegral (C v)]
    (_hrange : ∀ v, Set.range (i v) = v.val)
    (q : ∀ v, Over.mk (ComponentFamily.structureMap πX i v) ≅
      Over.mk (Scheme.ProjectiveLine.structureMap (IsLocalRing.ResidueField R)))
    (hprod : Degree.ProperCurveProductFormula.{u}),
    Flat πX → IsProper πX → Flat πZ → IsProper πZ →
    (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) →
    (∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z)) →
    topologicalKrullDim X = 2 → topologicalKrullDim Z = 2 →
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) →
    IsIso (Scheme.Pullback.GenericRestriction.genericRestriction (F := F) πX πZ f hf) →
    ¬ IsIso f → ∃ (v : irreducibleComponents (obj πX))
      (hcart : IsLocallyRankOne X (idealModule (surfaceInclusion πX i v))),
      normalDegree πX i q hprod v hcart = -1

/-- Under the original contraction family, absence of an actual minus-one
component forces this actual comparison morphism to be an isomorphism. -/
theorem noMinusOne_isIso (hcontraction : VerticalContractionExceptionalComponent.{u})
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
    (hprod : Degree.ProperCurveProductFormula.{u})
    [Flat πX] [IsProper πX] [Flat πZ] [IsProper πZ]
    (hregularX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hregularZ : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z))
    (hdimX : topologicalKrullDim X = 2) (hdimZ : topologicalKrullDim Z = 2)
    (hfield : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hgeneric : IsIso
      (Scheme.Pullback.GenericRestriction.genericRestriction (F := F) πX πZ f hf))
    (hminus : ∀ v hcart, normalDegree πX i q hprod v hcart ≠ -1) : IsIso f := by
  by_contra hnot
  obtain ⟨v, hcart, hv⟩ := hcontraction R F X Z πX πZ f hf C i hrange q hprod
    inferInstance inferInstance inferInstance inferInstance hregularX hregularZ
    hdimX hdimZ hfield hgeneric hnot
  exact hminus v hcart hv

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
