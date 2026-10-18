/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCoverDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalPullbackReflection
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! Exact field-stage projections and the faithfully flat functors used in gluing. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

universe u

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc] theorem fieldProjection_field (s : Finset Ω) :
    FieldLimit.fieldProjection K Ω p (op s) ≫
      pullback.fst (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p =
        pullback.snd p (Spec.algebraMap K Ω) ≫
          Spec.algebraMap (FieldLimit.finiteField K Ω s) Ω := by
  change (pullbackSymmetry p (Spec.algebraMap K Ω)).hom ≫
    pullback.lift
      (pullback.fst (Spec.algebraMap K Ω) p ≫
        Spec.algebraMap (FieldLimit.finiteField K Ω s) Ω)
      (pullback.snd (Spec.algebraMap K Ω) p) _ ≫ _ = _
  simp only [pullback.lift_fst, pullbackSymmetry_hom_comp_fst_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The exact standard-order field projection is a base change of the actual
inclusion of the finite intermediate field into Ω. -/
theorem fieldProjection_isPullback (s : Finset Ω) :
    IsPullback (FieldLimit.fieldProjection K Ω p (op s))
      (pullback.snd p (Spec.algebraMap K Ω))
      (pullback.fst (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p)
      (Spec.algebraMap (FieldLimit.finiteField K Ω s) Ω) := by
  apply IsPullback.of_right (h₁₂ := pullback.snd
    (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p)
    (h₂₂ := Spec.algebraMap K (FieldLimit.finiteField K Ω s))
  · have h : Spec.algebraMap (FieldLimit.finiteField K Ω s) Ω ≫
        Spec.algebraMap K (FieldLimit.finiteField K Ω s) = Spec.algebraMap K Ω := by
      rw [← Spec.map_comp]
      congr 1
    rw [h]
    change IsPullback (FieldLimit.fieldProjection K Ω p (op s) ≫
      ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom) _ _ _
    rw [FieldLimit.fieldProjection_base]
    exact IsPullback.of_hasPullback _ _
  · exact fieldProjection_field K Ω p s
  · exact (IsPullback.of_hasPullback _ _).flip

instance fieldProjection_flat (s : Finset Ω) :
    Flat (FieldLimit.fieldProjection K Ω p (op s)) :=
  MorphismProperty.of_isPullback (fieldProjection_isPullback K Ω p s).flip
    (inferInstanceAs (Flat (Spec.algebraMap (FieldLimit.finiteField K Ω s) Ω)))

instance fieldProjection_surjective (s : Finset Ω) :
    Surjective (FieldLimit.fieldProjection K Ω p (op s)) :=
  MorphismProperty.of_isPullback (fieldProjection_isPullback K Ω p s).flip
    (inferInstanceAs (Surjective (Spec.algebraMap (FieldLimit.finiteField K Ω s) Ω)))

instance fieldProjection_quasiCompact (s : Finset Ω) :
    QuasiCompact (FieldLimit.fieldProjection K Ω p (op s)) :=
  MorphismProperty.of_isPullback (fieldProjection_isPullback K Ω p s).flip
    (inferInstanceAs (QuasiCompact (Spec.algebraMap (FieldLimit.finiteField K Ω s) Ω)))

instance fieldProjection_pullback_faithful (s : Finset Ω) :
    (Over.pullback (FieldLimit.fieldProjection K Ω p (op s))).Faithful := inferInstance

instance fieldProjection_pullback_reflectsIsomorphisms (s : Finset Ω) :
    (Over.pullback (FieldLimit.fieldProjection K Ω p (op s))).ReflectsIsomorphisms :=
  PurelyInseparable.Global.overPullback_reflectsIsomorphisms _

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 aaa1f61eeab9571d80cb0f6d8a6e3d2b68292cc891e240755164012203581c65.
Definitions, hypotheses and universes are retained modulo native names. -/
