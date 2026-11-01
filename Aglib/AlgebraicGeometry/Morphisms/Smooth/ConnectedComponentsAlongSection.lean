/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Properties.Normal.PointComponentLift
public import Aglib.AlgebraicGeometry.Geometrically.Connected.RationalPoint
public import Mathlib.AlgebraicGeometry.Fiber

/-! # Actual smooth fibre components meeting a section

Over a field the original normal component through the section point is an
actual clopen connected component. The original section factors through it,
so its structural map is geometrically connected. Quasi-compactness is retained
when present. These field results do not assert openness of the union of the
components inside a relative family.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.SmoothSectionComponent
universe u
variable {k : Type u} [Field k] {Y : Scheme.{u}}
  (q : Y ⟶ Spec (.of k)) [Smooth q] (o : Spec (.of k) ⟶ Y)

/-- The component is the existing actual normal-component open, at the
original image of the field point. -/
def componentOpen : Y.Opens := by
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  exact normalComponentOpen Y (smoothFieldNormality k Y q inferInstance)
    (o (IsLocalRing.closedPoint k))

lemma mem_componentOpen : o (IsLocalRing.closedPoint k) ∈ componentOpen q o := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  exact mem_normalComponentOpen Y (smoothFieldNormality k Y q inferInstance) _

lemma componentOpen_isClosed : IsClosed (componentOpen q o : Set Y) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  exact normalComponentOpen_isClosed Y (smoothFieldNormality k Y q inferInstance) _

/-- This is the ordinary topological connected component, not a replacement
chosen connected model. -/
lemma componentOpen_eq_connectedComponent :
    (componentOpen q o : Set Y) = connectedComponent (o (IsLocalRing.closedPoint k)) := by
  let U := componentOpen q o
  have hx : o (IsLocalRing.closedPoint k) ∈ U := mem_componentOpen q o
  have hU : IsClopen (U : Set Y) := ⟨componentOpen_isClosed q o, U.isOpen⟩
  have hp : _root_.IsPreconnected (U : Set Y) :=
    isIrreducible_irreducibleComponent.2.isPreconnected
  exact (hp.connectedComponentIn hx).symm.trans (hU.connectedComponentIn_eq hx)

instance componentOpen_isIntegral : IsIntegral (componentOpen q o) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  dsimp [componentOpen]
  infer_instance

instance componentOpen_isClosedImmersion : IsClosedImmersion (componentOpen q o).ι := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  dsimp [componentOpen]
  infer_instance

/-- The original field point map factors through the very same component. -/
def sectionLift : Spec (.of k) ⟶ componentOpen q o := by
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  exact normalComponentLift Y (smoothFieldNormality k Y q inferInstance)
    (o (IsLocalRing.closedPoint k)) o rfl

@[reassoc]
lemma sectionLift_fac : sectionLift q o ≫ (componentOpen q o).ι = o := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  exact normalComponentLift_fac Y (smoothFieldNormality k Y q inferInstance) _ o rfl

lemma sectionLift_closedPoint :
    sectionLift q o (IsLocalRing.closedPoint k) =
      ⟨o (IsLocalRing.closedPoint k), mem_componentOpen q o⟩ := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  exact normalComponentLift_closedPoint Y (smoothFieldNormality k Y q inferInstance) _ o rfl

/-- The unchanged structural map on the actual component. -/
def componentMap : (componentOpen q o).toScheme ⟶ Spec (.of k) := (componentOpen q o).ι ≫ q

lemma sectionLift_componentMap (ho : o ≫ q = 𝟙 _) :
    sectionLift q o ≫ componentMap q o = 𝟙 _ :=
  (Category.assoc _ _ _).symm.trans ((congrArg (fun a => a ≫ q)
    (sectionLift_fac q o)).trans ho)

/-- Connectedness and the original lifted rational section supply genuine
geometric connectedness of the actual component. -/
theorem componentMap_geometricallyConnected (ho : o ≫ q = 𝟙 _) :
    GeometricallyConnected (componentMap q o) :=
  Geometrically.geometricallyConnected_of_connectedSpace_of_section
    (componentMap q o) (sectionLift q o) (sectionLift_componentMap q o ho)

instance componentMap_smooth : Smooth (componentMap q o) := by
  dsimp [componentMap]
  infer_instance

instance componentMap_quasiCompact [QuasiCompact q] : QuasiCompact (componentMap q o) := by
  dsimp [componentMap]
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSectionComponent

namespace AlgebraicGeometry.Scheme
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- The original section induces its actual residue-field section on each
original scheme-theoretic fibre. -/
def sectionOnFiber (s : S) : Spec (S.residueField s) ⟶ f.fiber s :=
  pullback.lift (S.fromSpecResidueField s ≫ σ) (𝟙 _) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

@[reassoc]
lemma sectionOnFiber_fiberι (s : S) :
    sectionOnFiber f σ hσ s ≫ f.fiberι s = S.fromSpecResidueField s ≫ σ :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma sectionOnFiber_structural (s : S) :
    sectionOnFiber f σ hσ s ≫ f.fiberToSpecResidueField s = 𝟙 _ :=
  pullback.lift_snd _ _ _

local instance fiber_structural_smooth [Smooth f] (s : S) :
    Smooth (f.fiberToSpecResidueField s) := by
  change Smooth (pullback.snd f (S.fromSpecResidueField s))
  infer_instance

/-- Each smooth fibre has its actual clopen section component, with genuinely
geometrically connected structural map. No relative openness is asserted. -/
theorem sectionComponentOnFiber_geometricallyConnected [Smooth f] (s : S) :
    GeometricallyConnected (@SmoothSectionComponent.componentMap
      (S.residueField s) inferInstance (f.fiber s) (f.fiberToSpecResidueField s)
      (fiber_structural_smooth f s) (sectionOnFiber f σ hσ s)) := by
  exact @SmoothSectionComponent.componentMap_geometricallyConnected
    (S.residueField s) inferInstance (f.fiber s) (f.fiberToSpecResidueField s)
    (fiber_structural_smooth f s) (sectionOnFiber f σ hσ s)
    (sectionOnFiber_structural f σ hσ s)

end AlgebraicGeometry.Scheme
