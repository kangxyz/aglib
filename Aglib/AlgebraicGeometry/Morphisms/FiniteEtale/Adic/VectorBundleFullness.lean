/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CompletionFullness
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.VectorBundleMaps
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FiniteFlat
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.LocallyFree

/-! # Finite-etale fullness from the original scalar section cone

Finite flat cover algebras supply the finite locally free coefficients
internally. The original algebra-map packet and its geometric reconstruction
are unchanged; no coherent-completion fullness premise is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonObj AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

open Modules Modules.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [X.IsQuasiAffine]
  (K : X.IdealSheafData)
  (hunit : IsLimit (idealSheafSectionCone X K (SheafOfModules.unit X.ringCatSheaf)))

omit [X.IsQuasiAffine] in
/-- The original cover algebra is finite locally free, without choosing a new module. -/
theorem globalStructure_finiteLocallyFree (C : FiniteEtale X) :
    IsFiniteLocallyFree X (globalStructureCoherent C).obj :=
  finiteFlat_pushforwardStructureSheaf_isFiniteLocallyFree C.obj.hom

/-- Construct the original global algebra-map packet using only scalar completeness. -/
def vectorBundleGlobalAlgebraMapData {C D : FiniteEtale X}
    (t : CoverSystem.Hom (restrictionCoverSystem K C) (restrictionCoverSystem K D)) :
    { u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf D.obj.hom)
        (pushforwardStructureSheaf C.obj.hom) //
      IsMonHom (C := X.Modules) u ∧
      (Functor.const ℕᵒᵖ).map u ≫ restrictionModuleUnit K C =
        restrictionModuleUnit K D ≫ t.adicMap.hom } := by
  let : IsFiniteLocallyFree X (globalAlgebraizationData K C).coherent.obj := by
    change IsFiniteLocallyFree X (globalStructureCoherent C).obj
    exact globalStructure_finiteLocallyFree C
  let : IsFiniteLocallyFree X (globalAlgebraizationData K D).coherent.obj := by
    change IsFiniteLocallyFree X (globalStructureCoherent D).obj
    exact globalStructure_finiteLocallyFree D
  let : IsFiniteLocallyFree X
      ((globalAlgebraizationData K D).coherent.obj ⊗
        (globalAlgebraizationData K D).coherent.obj) :=
    finiteLocallyFree_tensor _ _
  let l := vectorBundleAlgebraizationMapData hunit
    (globalAlgebraizationData K D) (globalAlgebraizationData K C) t.adicMap
  refine ⟨l.val.hom.hom, l.val.hom.isMonHom_hom, ?_⟩
  simpa only [globalAlgebraizationData_quotientMaps] using l.property

include hunit in
/-- Every original first-stage cover morphism lifts from scalar section completeness. -/
theorem firstStage_baseChange_full_of_unitSectionCone :
    (baseChange (K ^ 1).subschemeι).Full := by
  constructor
  intro C D a
  obtain ⟨t, ht, _⟩ := CoverSystem.existsUnique_homOfFirstStage
    (restrictionCoverSystem K C) (restrictionCoverSystem K D) a
  obtain ⟨g, hg⟩ := exists_globalMap_of_originalAlgebraPacket K t
    (vectorBundleGlobalAlgebraMapData K hunit t)
  exact ⟨g, hg.trans ht⟩

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
