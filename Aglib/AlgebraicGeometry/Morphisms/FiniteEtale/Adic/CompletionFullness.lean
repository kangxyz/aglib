/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.GlobalAlgebraData
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoverSystemHomModules
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CompletionNaturality
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.AlgebraHomReconstruction
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.Maps

/-!
# Fullness of restriction from coherent completion

An arbitrary first-stage cover map lifts through the original nilpotent tower.
Coherent completion lifts its native algebra map, affine reconstruction gives
the actual global cover map, and the original epimorphic reduction detects its
prescribed first-stage restriction. No essential-surjectivity input is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open scoped MonObj AlgebraicGeometry.Scheme.Modules.Algebra

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

universe u

open Modules Modules.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (K : X.IdealSheafData)

/-- Lift the whole original algebra-map packet before specializing the geometric
reconstruction. The primitive module carrier and all quotient equations stay together. -/
def originalGlobalAlgebraMapData (hFF : (completionFunctor X K).FullyFaithful)
    {C D : FiniteEtale X}
    (t : CoverSystem.Hom (restrictionCoverSystem K C) (restrictionCoverSystem K D)) :
    { u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf D.obj.hom)
        (pushforwardStructureSheaf C.obj.hom) //
      IsMonHom (C := X.Modules) u ∧
      (Functor.const ℕᵒᵖ).map u ≫ restrictionModuleUnit K C =
        restrictionModuleUnit K D ≫ t.adicMap.hom } := by
  let l := algebraizationMapData hFF
    (globalAlgebraizationData K D) (globalAlgebraizationData K C) t.adicMap
  refine ⟨l.val.hom.hom, l.val.hom.isMonHom_hom, ?_⟩
  simpa only [globalAlgebraizationData_quotientMaps] using l.property

/-- The actual original restriction maps are epimorphisms. -/
theorem restrictionModuleUnit_epi (C : FiniteEtale X) (n : ℕ) :
    Epi (C := X.Modules) ((restrictionModuleUnit K C).app (op n)) := by
  rw [← unit_restrictionCompletionIso_hom]
  change Epi (C := X.Modules)
    ((idealSheafQuotientUnit X (K ^ n)).app (globalStructureCoherent C).obj ≫
      ((restrictionCompletionData K C).val.app (op n)).hom)
  infer_instance

/-- Detect the actual first-stage map from the original quotient equation,
with both the tower morphism and the global geometric morphism still abstract. -/
theorem firstStage_eq_of_originalModuleEquation {C D : FiniteEtale X}
    (t : CoverSystem.Hom (restrictionCoverSystem K C) (restrictionCoverSystem K D))
    (g : C ⟶ D)
    (h : Modules.Algebra.structurePullbackMap (p := D.obj.hom) (q := C.obj.hom)
        g.hom.left g.hom.w ≫ (restrictionModuleUnit K C).app (op 1) =
      (restrictionModuleUnit K D).app (op 1) ≫ t.adicMap.hom.app (op 1)) :
    (baseChange (K ^ 1).subschemeι).map g = t.stage 1 := by
  let := restrictionModuleUnit_epi K D 1
  have hm : (Modules.Algebra.structureSheafFunctor X).map
      (restrictionStageMorphism K g 1).op = t.adicMap.hom.app (op 1) := by
    apply (cancel_epi ((restrictionModuleUnit K D).app (op 1))).mp
    exact (restrictionModuleUnit_map K g 1).trans h
  let : IsFinite ((restrictionCoverSystem K C).ambientMap 1) := by
    dsimp only [CoverSystem.ambientMap]
    infer_instance
  let : IsFinite ((restrictionCoverSystem K D).ambientMap 1) := by
    dsimp only [CoverSystem.ambientMap]
    infer_instance
  have hs : restrictionStageMorphism K g 1 = t.ambientStage 1 := by
    let : IsAffineHom (Over.mk ((restrictionCoverSystem K C).ambientMap 1)).hom := by
      change IsAffineHom ((restrictionCoverSystem K C).ambientMap 1)
      infer_instance
    let : IsAffineHom (Over.mk ((restrictionCoverSystem K D).ambientMap 1)).hom := by
      change IsAffineHom ((restrictionCoverSystem K D).ambientMap 1)
      infer_instance
    apply Modules.Algebra.structurePullbackMap_over_injective
    exact hm
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact congrArg (fun k => k.left) hs

/-- Geometrically realize an arbitrary original algebra-map packet, keeping the
packet abstract throughout reconstruction and first-stage detection. -/
theorem exists_globalMap_of_originalAlgebraPacket {C D : FiniteEtale X}
    (t : CoverSystem.Hom (restrictionCoverSystem K C) (restrictionCoverSystem K D))
    (l : { u : Scheme.Modules.Hom (X := X) (pushforwardStructureSheaf D.obj.hom)
        (pushforwardStructureSheaf C.obj.hom) //
      IsMonHom (C := X.Modules) u ∧
      (Functor.const ℕᵒᵖ).map u ≫ restrictionModuleUnit K C =
        restrictionModuleUnit K D ≫ t.adicMap.hom }) :
    ∃ g : C ⟶ D, (baseChange (K ^ 1).subschemeι).map g = t.stage 1 := by
  let : IsMonHom (C := X.Modules) l.val := l.property.1
  obtain ⟨g₀, hg₀, _⟩ := Modules.Algebra.existsUnique_structurePullbackMap_over
    (P := C.obj) (Q := D.obj) l.val
  let g : C ⟶ D := ObjectProperty.homMk g₀
  refine ⟨g, ?_⟩
  have h : Modules.Algebra.structurePullbackMap (p := D.obj.hom) (q := C.obj.hom)
      g.hom.left g.hom.w ≫ (restrictionModuleUnit K C).app (op 1) =
      (restrictionModuleUnit K D).app (op 1) ≫ t.adicMap.hom.app (op 1) := by
    exact (congrArg (fun k : Scheme.Modules.Hom (X := X)
      (pushforwardStructureSheaf D.obj.hom) (pushforwardStructureSheaf C.obj.hom) =>
        CategoryStruct.comp (obj := X.Modules) k
          ((restrictionModuleUnit K C).app (op 1))) hg₀).trans
      (NatTrans.congr_app l.property.2 (op 1))
  exact firstStage_eq_of_originalModuleEquation K t g h

/-- Coherent completion lifts every actual first-stage finite-etale morphism. -/
theorem firstStage_baseChange_full (hFF : (completionFunctor X K).FullyFaithful) :
    (baseChange (K ^ 1).subschemeι).Full := by
  constructor
  intro C D a
  obtain ⟨t, ht, _⟩ := CoverSystem.existsUnique_homOfFirstStage
    (restrictionCoverSystem K C) (restrictionCoverSystem K D) a
  obtain ⟨g, hg⟩ := exists_globalMap_of_originalAlgebraPacket K t
    (originalGlobalAlgebraMapData K hFF t)
  exact ⟨g, hg.trans ht⟩

end AlgebraicGeometry.Scheme.FiniteEtale.Adic
