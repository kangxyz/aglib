/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FiniteType.TargetOpenSystems
public import Aglib.AlgebraicGeometry.Descent.FiniteType.SeparatedAffineTarget

/-!
# Eventual separatedness on a fixed affine target open

Quasi-separatedness of the fixed target and compactness of source stages
make the actual inverse-image chart stages compact. The native restricted
system satisfies the affine-target theorem. Actual pullback comparisons
identify its separated structural maps with the usual target restrictions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.TargetOpenSystem

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
  {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S)
  (i : I) (V : S.Opens)

/-- Compact sources and a quasi-separated fixed target make the actual
affine-target inverse-image chart stages compact. -/
lemma compactSpace_obj [∀ j, CompactSpace (D.obj j)] [QuasiSeparatedSpace S]
    (hV : IsAffineOpen V) (j : Over i) :
    CompactSpace ((opensDiagram D i (t.app i ⁻¹ᵁ V)).obj j) := by
  have : QuasiCompact (t.app j.left) :=
    @quasiCompact_of_compactSpace (D.obj j.left) S (t.app j.left)
      (inferInstanceAs (CompactSpace (D.obj j.left))) inferInstance
  apply isCompact_iff_compactSpace.mp
  change IsCompact (D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V) : Set (D.obj j.left))
  rw [stageOpen_eq]
  exact (t.app j.left).isCompact_preimage hV.isCompact

/-- Quasi-separatedness of chart stages is inherited by the actual opens. -/
lemma quasiSeparatedSpace_obj [∀ j, QuasiSeparatedSpace (D.obj j)] (j : Over i) :
    QuasiSeparatedSpace ((opensDiagram D i (t.app i ⁻¹ᵁ V)).obj j) :=
  (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ (t.app i ⁻¹ᵁ V)).isOpen).mp
    (.of_quasiSeparatedSpace _)

/-- The actual restricted limit map is separated by its cartesian square. -/
lemma isSeparated_limitMap (c : Cone D) (h : c.pt ⟶ S)
    (hcompat : ∀ j, c.π.app j ≫ t.app j = h) [IsSeparated h] :
    IsSeparated (limitMap D t i V c h hcompat) := by
  rw [← (isPullback_limitMap D t i V c h hcompat).isoPullback_hom_fst]
  infer_instance

/-- Separatedness of the actual stage map transports to the usual target
restriction through the two explicit canonical pullback comparisons. -/
lemma isSeparated_restriction_of_stageMap (j : Over i)
    [IsSeparated (stageMap D t i V j)] : IsSeparated (t.app j.left ∣_ V) := by
  have : IsSeparated (pullback.fst V.ι (t.app j.left)) := by
    rw [← (isPullback_stageMap D t i V j).isoPullback_inv_fst]
    infer_instance
  rw [← (isPullback_morphismRestrict (t.app j.left) V).isoPullback_hom_fst]
  infer_instance

/-- Separatedness descends on one actual affine target-open system. -/
lemma exists_isSeparated_stageMap [IsCofiltered I]
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    [QuasiSeparatedSpace S] (hV : IsAffineOpen V)
    (c : Cone D) (hc : IsLimit c) (h : c.pt ⟶ S)
    (hcompat : ∀ j, c.π.app j ≫ t.app j = h) [IsSeparated h] :
    ∃ j : Over i, IsSeparated (stageMap D t i V j) := by
  have : IsAffine V.toScheme := hV
  have (j : Over i) : CompactSpace ((opensDiagram D i (t.app i ⁻¹ᵁ V)).obj j) :=
    compactSpace_obj D t i V hV j
  have (j : Over i) : QuasiSeparatedSpace ((opensDiagram D i (t.app i ⁻¹ᵁ V)).obj j) :=
    quasiSeparatedSpace_obj D t i V j
  have := isSeparated_limitMap D t i V c h hcompat
  obtain ⟨j, hj⟩ := Scheme.exists_isSeparated_app_of_isLimit_of_isAffine_target
    (opensDiagram D i (t.app i ⁻¹ᵁ V)) (structureMap D t i V)
    (opensCone D c i (t.app i ⁻¹ᵁ V)) (isLimitOpensCone D c hc i (t.app i ⁻¹ᵁ V))
    (limitMap D t i V c h hcompat) (cone_compatibility D t i V c h hcompat)
    (Over.mk (𝟙 i))
  exact ⟨j.left, hj⟩

end AlgebraicGeometry.Scheme.TargetOpenSystem
