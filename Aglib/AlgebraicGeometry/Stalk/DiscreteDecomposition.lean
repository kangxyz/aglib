/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Discrete schemes as the coproduct of their actual stalk spectra

The comparison is the original `Sigma.desc` of `fromSpecStalk`. Nilpotents
are preserved. In particular this applies to genuine Artinian schemes,
without replacing them by their reduced points or residue fields.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Function

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [DiscreteTopology X]

/-- On a discrete scheme the original local-spectrum map is an open immersion. -/
theorem fromSpecStalk_isOpenImmersion_of_discrete (x : X) :
    IsOpenImmersion (X.fromSpecStalk x) := by
  let : Flat (X.fromSpecStalk x) := fromSpecStalk_flat X x
  let : ∀ p, IsIso ((X.fromSpecStalk x).stalkMap p) :=
    fun p => Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ p
  exact IsOpenImmersion.of_isIso_stalkMap _
    (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (X.fromSpecStalk x).continuous (X.fromSpecStalk x).isEmbedding.injective
      (fun _ _ => isOpen_discrete _))

/-- The original local-spectrum map has exactly its designated point as image. -/
theorem range_fromSpecStalk_of_discrete (x : X) :
    Set.range (X.fromSpecStalk x) = {x} := by
  rw [range_fromSpecStalk]
  ext y
  simp

/-- The original sum of local-spectrum maps is an isomorphism for a discrete scheme. -/
theorem stalkCoproductMap_isIso :
    IsIso (Sigma.desc (fun x : X => X.fromSpecStalk x)) := by
  let : ∀ x : X, IsOpenImmersion (X.fromSpecStalk x) :=
    fromSpecStalk_isOpenImmersion_of_discrete X
  have hcov : ⨆ x : X, (X.fromSpecStalk x).opensRange = ⊤ := by
    apply top_le_iff.mp
    intro y _
    apply Opens.mem_iSup.mpr
    refine ⟨y, ?_⟩
    change y ∈ Set.range (X.fromSpecStalk y)
    exact ⟨IsLocalRing.closedPoint (X.presheaf.stalk y), fromSpecStalk_closedPoint⟩
  have hdisj : Pairwise (Disjoint on (fun x : X => (X.fromSpecStalk x).opensRange)) := by
    intro x y hxy
    apply Opens.coe_disjoint.mp
    change Disjoint (Set.range (X.fromSpecStalk x)) (Set.range (X.fromSpecStalk y))
    rw [range_fromSpecStalk_of_discrete, range_fromSpecStalk_of_discrete]
    exact Set.disjoint_singleton.mpr hxy
  exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
    (Cofan.mk X (fun x : X => X.fromSpecStalk x))).mp
      (nonempty_isColimit_cofanMk_of (fun x : X => X.fromSpecStalk x) hcov hdisj)

/-- The actual stalk-spectrum coproduct is canonically the original discrete scheme. -/
def stalkCoproductIso : (∐ fun x : X => Spec (X.presheaf.stalk x)) ≅ X := by
  let := stalkCoproductMap_isIso X
  exact asIso (Sigma.desc (fun x : X => X.fromSpecStalk x))

@[reassoc (attr := simp)]
theorem stalkCoproductIso_component (x : X) :
    Sigma.ι (fun x : X => Spec (X.presheaf.stalk x)) x ≫ (stalkCoproductIso X).hom =
      X.fromSpecStalk x :=
  Sigma.ι_comp_desc _ _

end AlgebraicGeometry.Scheme
