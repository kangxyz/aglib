/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Descent.Limit
public import Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Henselian.Selected
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ResidueStageComparison
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ResidueBaseChangeProperties

/-!
# Actual line-bundle descent through marked arithmetic residue stages

The original closed fibre is the existing marked residue-field limit. An
actual line bundle descends to one stage, lifts on its selected local
henselization, and pulls back through the original marked prime-fibre map.
The local lifting hypothesis remains explicit in this intermediate reduction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Invertible

open Algebra.FiniteTypeSubalgebraLimit LocalRing LocalRing.AtLocalTarget

universe u

/-- Lifting on the actual selected geometric henselizations gives lifting
on the original arbitrary henselian target of a qcqs coefficient model. -/
theorem exists_lineBundle_lift_of_residueStage_lifts
    (B R : Type u) [CommRing B] [CommRing R] [Algebra B R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [QuasiCompact f] [QuasiSeparated f]
    (hlift : ∀ s : Finset R,
      Function.Surjective (pullbackClass (Limits.pullback.fst
        (Limits.pullback.snd f (henselizationSpecMap
          (stage B R s).val.toRingHom (algebraMap B (stage B R s))))
        (residueSpecMap (Henselization.AtLocalTarget.Ring (stage B R s).val.toRingHom)))))
    (L : LineBundle (Limits.pullback
      (Limits.pullback.snd f (Spec.algebraMap B R)) (residueSpecMap R))) :
    ∃ W : LineBundle (Limits.pullback f (Spec.algebraMap B R)),
      Nonempty ((pullback (Limits.pullback.fst
        (Limits.pullback.snd f (Spec.algebraMap B R)) (residueSpecMap R))).obj W.val ≅ L.val) := by
  refine exists_lineBundle_lift_of_stage_lifts
    (FiniteTypeResidueLimit.schemeDiagram B R (IsLocalRing.maximalIdeal R) f)
    (FiniteTypeResidueLimit.schemeCone B R (IsLocalRing.maximalIdeal R) f)
    (FiniteTypeResidueLimit.schemeConeIsLimit B R (IsLocalRing.maximalIdeal R) f)
    (Limits.pullback.fst (Limits.pullback.snd f (Spec.algebraMap B R)) (residueSpecMap R))
    (FiniteTypeResidueLimit.localClosedFiberIso B R f) ?_ L
  intro s C
  let S := stage B R s.unop
  let a : S →+* R := (stage B R s.unop).val.toRingHom
  let b : B →+* S := algebraMap B S
  let e : primeFiber a b f ≅
      (FiniteTypeResidueLimit.schemeDiagram B R (IsLocalRing.maximalIdeal R) f).obj s :=
    pullbackSymmetry f (Spec.algebraMap B
      (Localization.AtLocalTarget.prime a).ResidueField)
  obtain ⟨W, ⟨hW⟩⟩ := exists_lineBundle_of_selected_henselization a b f
    (exists_lineBundle_lift_of_pullbackClass_surjective _ (hlift s.unop))
    (pullbackLineBundle e.hom C)
  refine ⟨W, ⟨hW ≪≫ (pullbackComp (targetPrimeFiberMap a b f) e.hom).app C.val ≪≫ ?_⟩⟩
  exact (pullbackCongr
    (FiniteTypeResidueLimit.targetPrimeFiberMap_eq_projection B R f s.unop)).app C.val

end AlgebraicGeometry.Scheme.Modules.Invertible
