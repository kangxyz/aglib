/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FieldLimit
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.PurelyInseparablePoints
public import Aglib.AlgebraicGeometry.FundamentalGroup.SeparableStage

/-!
# FiniteBasePoint

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber)

namespace AlgebraicGeometry.Scheme.FiniteEtale.FiniteBasePoint

universe u
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypotheses and binder order.
/-- An actual point of a finite étale base cover descends to a finite field
inside Ω, using the proved field limit and actual morphism descent. -/
-- Keep the original supplied class/data inputs and binder order of this interface.
@[nolint unusedArguments]
theorem exists_finite_field_point (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) :
    ∃ (s : Finset Ω) (qE : Fiber (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) Z),
      Spec.map (CommRingCat.ofHom (FieldLimit.finiteField K Ω s).val.toRingHom) ≫ qE.left =
        q.left := by
  let D := FieldLimit.fieldDiagram K Ω
  let c := FieldLimit.fieldCone K Ω
  have (s : (Finset Ω)ᵒᵖ) : CompactSpace (D.obj s).left :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of (FieldLimit.finiteField K Ω s.unop))))
  have (s : (Finset Ω)ᵒᵖ) : QuasiSeparatedSpace (D.obj s).left :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of (FieldLimit.finiteField K Ω
      s.unop))))
  have {s t : (Finset Ω)ᵒᵖ} (f : s ⟶ t) : IsAffineHom (D.map f).left := by
    change IsAffineHom (Spec.map ((FieldLimit.ringDiagram K Ω).map f.unop))
    infer_instance
  obtain ⟨s, qE, he⟩ := LimitDescent.exists_hom_to_cover D c
    (FieldLimit.fieldConeIsLimit K Ω) Z q
  exact ⟨s.unop, qE, congrArg (fun z ↦ z.left) he⟩

theorem descend_point_pure (S E : Type u) [Field S] [Field E]
    [Algebra K S] [Algebra S E] [Algebra K E] [IsScalarTower K S E]
    [IsPurelyInseparable S E] (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (qE : Fiber (Spec.algebraMap K E) Z) :
    ∃ qS : Fiber (Spec.algebraMap K S) Z, Spec.algebraMap S E ≫ qS.left = qE.left := by
  have hcomp := SeparableStage.specTower K S E
  let qE' : Fiber (Spec.algebraMap S E ≫ Spec.algebraMap K S) Z :=
    Over.homMk qE.left ((Over.w qE).trans hcomp.symm)
  obtain ⟨qS, hqS⟩ := PurelyInseparable.extendFiber_surjective S E (Spec.algebraMap K S) Z qE'
  exact ⟨qS, congrArg (fun z ↦ z.left) hqS⟩

/-- The selected point already descends to the maximal separable subfield of
that finite field. The equation is precomposition by the actual field maps. -/
theorem exists_separable_field_point (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) :
    ∃ (s : Finset Ω)
      (qS : Fiber (Spec.algebraMap K (separableClosure K (FieldLimit.finiteField K Ω s))) Z),
      (Spec.map (CommRingCat.ofHom (FieldLimit.finiteField K Ω s).val.toRingHom) ≫
          Spec.algebraMap (separableClosure K (FieldLimit.finiteField K Ω s))
            (FieldLimit.finiteField K Ω s)) ≫ qS.left = q.left := by
  obtain ⟨s, qE, hqE⟩ := exists_finite_field_point K Ω Z q
  obtain ⟨qS, hs⟩ := descend_point_pure K
    (separableClosure K (FieldLimit.finiteField K Ω s)) (FieldLimit.finiteField K Ω s) Z qE
  refine ⟨s, qS, ?_⟩
  rw [Category.assoc, hs]
  exact hqE

end AlgebraicGeometry.Scheme.FiniteEtale.FiniteBasePoint

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 36b9c4291e5b394188625a0221fcac3204eba3eaf5235a553f48a2121c1a5b90.
Definitions, hypotheses and universes are retained modulo native names. -/
