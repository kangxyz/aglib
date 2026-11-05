/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FilteredPresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FreeRepresentablePullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteColimits
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineRepresentable

/-! # Constructibility of the native fixed-ring finite-colimit stages

The original affine étale generators admit actual finite étale partitions over
a separated scheme. Their native finite-colimit closure is therefore
geometrically constructible. This is a theorem about the existing stage
predicate, not a new definition of constructibility.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation

universe u

attribute [local instance] ModuleCat.Sheaf.hasSheafify Cardinal.fact_isRegular_aleph0

variable (R : Type (u + 1)) [Ring R] [IsNoetherianRing R]
    {X : Scheme.{u}} [X.IsSeparated]

/-- The native finite-colimit stages are genuinely constructible module sheaves. -/
theorem finiteColimitStage_isConstructible
    (F : ModuleSheaf R X) (hF : finiteColimitStages R X F) : IsConstructible F := by
  have hgen : generators R X ≤ (IsConstructible (R := R) (X := X)) := by
    rintro M ⟨U⟩
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj U).left :=
      inferInstanceAs (IsAffine (Spec U.left.unop))
    exact freeModule_isConstructible_of_finiteEtalePartitions R _
      (PositivePresentation.finiteEtalePartitions_of_isAffine_of_isSeparated _)
  have hclosure : finiteColimitStages R X ≤ (IsConstructible (R := R) (X := X)) := by
    apply (generators R X).colimitsCardinalClosure_le Cardinal.aleph0.{u + 1} ?_ hgen
    intro J _ hJ
    let : Finite (Arrow J) := (hasCardinalLT_aleph0_iff _).mp hJ
    exact {
      colimitsOfShape_le := by
        rintro G ⟨p⟩
        exact Modules.isConstructible_of_isColimit p.diag p.isColimit p.prop_diag_obj }
  exact hclosure F hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation
