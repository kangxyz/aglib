/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoverSystem
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.StageModuleComparison

/-!
# Actual coherent direct-image modules of the nilpotent cover tower

The diagram retains the original contravariant structure-module maps of the
actual cover diagram. Finite direct image supplies coherence, the original
closed-stage inclusion supplies annihilation, and actual affine base change
supplies reduction together with its quotient-unit equation. This constructs
adicity rather than requiring it from the prescribed closed-fibre cover.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic.CoverSystem

universe u

open Modules Modules.Coherent

variable {X : Scheme.{u}} {K : X.IdealSheafData} (T : CoverSystem K)

/-- The actual cover successor is also the actual ambient-stage pullback. -/
theorem transition_ambient_isPullback (n : ℕ) :
    IsPullback (T.transition n) (T.cover n).obj.hom
      (T.ambientMap (n + 1)) (K ^ n).subschemeι := by
  have H : IsPullback (stageMap K (Nat.le_succ n)) (𝟙 (K ^ n).subscheme)
      (K ^ (n + 1)).subschemeι (K ^ n).subschemeι :=
    (IsPullback.of_horiz_isIso_mono
      (show CommSq (𝟙 (K ^ n).subscheme) (stageMap K (Nat.le_succ n))
        (K ^ n).subschemeι (K ^ (n + 1)).subschemeι from ⟨by simp⟩)).flip
  simpa only [Category.comp_id] using (T.transition_isPullback n).paste_vert H

/-- The original direct-image structure modules and their original inverse maps. -/
def moduleDiagram : ℕᵒᵖ ⥤ X.Modules :=
  T.diagram.op ⋙ Modules.Algebra.structureSheafFunctor X

@[simp]
theorem moduleDiagram_obj (n : ℕ) :
    T.moduleDiagram.obj (op n) = pushforwardStructureSheaf (T.ambientMap n) := rfl

@[simp]
theorem moduleDiagram_map_succ (n : ℕ) :
    T.moduleDiagram.map (homOfLE (Nat.le_succ n)).op =
      Modules.Algebra.structurePullbackMap (T.transition n) (T.transition_ambientMap n) := by
  simp only [moduleDiagram, Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, diagram,
    Functor.ofSequence_map_homOfLE_succ]
  rfl

/-- Each stage carries the native direct-image algebra multiplication and unit. -/
instance instMonObjModuleDiagram (n : ℕᵒᵖ) : MonObj (C := X.Modules) (T.moduleDiagram.obj n) :=
  Modules.Algebra.pushforwardStructureSheafMonObj (T.ambientMap n.unop)

/-- The original finite-cover stage algebra is commutative. -/
instance instIsCommMonObjModuleDiagram (n : ℕᵒᵖ) :
    IsCommMonObj (C := X.Modules) (T.moduleDiagram.obj n) :=
  Modules.Algebra.pushforwardStructureSheafIsCommMonObj (T.ambientMap n.unop)

/-- Every original cover transition preserves the stage algebra operations. -/
instance instIsMonHomModuleDiagramMap {m n : ℕᵒᵖ} (g : m ⟶ n) :
    IsMonHom (C := X.Modules) (T.moduleDiagram.map g) :=
  Modules.Algebra.instIsMonHomStructureSheafFunctorMap (T.diagram.op.map g)

/-- Every original stage module is coherent because its ambient structural map is finite. -/
theorem moduleDiagram_coherent (n : ℕ) :
    QuasiCoherent.affineLocallyFiniteType X (T.moduleDiagram.obj (op n)) := by
  let : IsFinite (T.ambientMap n) := by dsimp only [ambientMap]; infer_instance
  exact Modules.Algebra.affineLocallyFiniteType_pushforwardStructureSheaf (T.ambientMap n)

/-- The original stage inclusion annihilates the actual stage module. -/
theorem moduleDiagram_annihilated (n : ℕ) :
    killedByIdealSheaf (K ^ n) (T.moduleDiagram.obj (op n)) := by
  apply killedByIdealSheaf_of_le _
    (killedByIdealSheaf_pushforward_ker (T.ambientMap n) (SheafOfModules.unit _))
  simpa only [IdealSheafData.ker_subschemeι] using
    Scheme.Hom.le_ker_comp (T.cover n).obj.hom (K ^ n).subschemeι

/-- The actual quotient comparison and its original successor equation are
one projection packet, before the formal-system constructor is applied. -/
def moduleReductionData (n : ℕ) :
    {e : (idealSheafQuotientFunctor X (K ^ n)).obj
      (T.moduleDiagram.obj (op (n + 1))) ≅ T.moduleDiagram.obj (op n) //
      (idealSheafQuotientUnit X (K ^ n)).app
        (T.moduleDiagram.obj (op (n + 1))) ≫ e.hom =
          T.moduleDiagram.map (homOfLE (Nat.le_succ n)).op} := by
  let : IsFinite (T.ambientMap (n + 1)) := by dsimp only [ambientMap]; infer_instance
  refine ⟨(cartesianStructureComparisonData (T.ambientMap (n + 1))
    (K ^ n).subschemeι (T.transition n) (T.cover n).obj.hom
    (T.transition_ambient_isPullback n)).val, ?_⟩
  rw [moduleDiagram_map_succ]
  exact (cartesianStructureComparisonData (T.ambientMap (n + 1))
    (K ^ n).subschemeι (T.transition n) (T.cover n).obj.hom
    (T.transition_ambient_isPullback n)).property

/-- The original module diagram satisfies all native adic-system conditions. -/
theorem moduleDiagram_isAdicSystem : IsAdicSystem X K T.moduleDiagram where
  coherent := T.moduleDiagram_coherent
  annihilated := T.moduleDiagram_annihilated
  reduction n := ⟨(T.moduleReductionData n).val, (T.moduleReductionData n).property⟩

/-- The actual coherent direct-image adic system of the original cover tower. -/
abbrev adicSystem [IsLocallyNoetherian X] : AdicSystem X K :=
  ⟨T.moduleDiagram, T.moduleDiagram_isAdicSystem⟩

/-- Index zero is the zero direct-image module, as required by the native convention. -/
theorem moduleDiagram_zero_isZero [IsLocallyNoetherian X] :
    IsZero (T.moduleDiagram.obj (op 0)) :=
  T.adicSystem.zero_isZero

end AlgebraicGeometry.Scheme.FiniteEtale.Adic.CoverSystem
