/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.BidualLine.ModelChart
public import Aglib.AlgebraicGeometry.Modules.Invertible.Locus


/-!
# The actual differential bidual line on the regular model

The original ordinary differential basis and the original birational model
derive the actual global bidual line. Nonempty affine charts are selected
through each point, and native local-rank-one descent glues the proved chart
property. No separate generic-rank or invertibility premise is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials

universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  {Λ A : CommRingCat.{u}} [IsDomain A]
  (ρ : Λ ⟶ A) (β : X ⟶ Spec A) [IsDominant β]
  [LocallyOfFiniteType (β ≫ Spec.map ρ)]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
  (hX : RegularStalks X) (hdX : topologicalKrullDim X ≤ 2)
  (n : ℕ) (b : Module.Basis (Fin n) A (CommRingCat.KaehlerDifferential ρ))

include hβ hX hdX b in
/-- The original raw top-form sheaf has an actual invertible bidual on the
regular surface model, with generic degree derived from the original basis. -/
theorem model_bidualForms_isLocallyRankOne :
    Invertible.IsLocallyRankOne X
      (Invertible.dualSheaf X (Invertible.dualSheaf X
        (moduleExteriorPower X (relativeDifferentialSheaf (β ≫ Spec.map ρ)) n))) := by
  let M : X.Modules := Invertible.dualSheaf X (Invertible.dualSheaf X
    (moduleExteriorPower X (relativeDifferentialSheaf (β ≫ Spec.map ρ)) n))
  apply Invertible.isLocallyRankOne_of_forall_isLocallyRankOneAt M
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : IsOpenImmersion hU.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec hU
  have hline := modelChart_bidualForms_isLocallyRankOne ρ β hβ hX hdX hU.fromSpec n b
  refine ⟨Spec Γ(X, U), hU.fromSpec, inferInstance, ?_, ?_⟩
  · rw [hU.range_fromSpec]
    exact hxU
  · exact Invertible.isLocallyRankOne_of_iso _
      ((restrictFunctorIsoPullback hU.fromSpec).app M) hline

/-- The actual bidual sheaf, packaged with its proved line property; no
replacement line or trivialization is selected. -/
def modelDifferentialLine : Invertible.LineBundle X :=
  ⟨Invertible.dualSheaf X (Invertible.dualSheaf X
      (moduleExteriorPower X (relativeDifferentialSheaf (β ≫ Spec.map ρ)) n)),
    model_bidualForms_isLocallyRankOne ρ β hβ hX hdX n b⟩

end AlgebraicGeometry.Scheme.Modules.Differentials
