/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinEtalePoints

/-!
# Generic-point indexing of the actual etale generic pullbacks

The bijection is induced by the original pullback projections. Its inverse
uses the canonical map of actual stalk spectra, retaining nilpotents.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {U X : Scheme.{u}} (f : U ⟶ X) [IsLocallyNoetherian X] [Etale f] [QuasiCompact f]

/-- The actual projection on the sigma family of generic pullback points. -/
def genericEtaleIndexMap (p : Σ η : genericPoints X, genericEtaleComponent f η) :
    genericPoints U :=
  ⟨(pullback.fst f (X.fromSpecStalk p.1.val)) p.2,
    genericEtaleComponent_projection_generic f p.1 p.2⟩

/-- Original pullback projections give a bijection with the generic points of the test. -/
theorem genericEtaleIndexMap_bijective : Function.Bijective (genericEtaleIndexMap f) := by
  constructor
  · rintro ⟨η, p⟩ ⟨θ, q⟩ h
    have hv := congrArg Subtype.val h
    have hb : η = θ := by
      apply Subtype.ext
      exact (genericEtaleComponent_projection_image f η p).symm.trans
        ((congrArg f hv).trans (genericEtaleComponent_projection_image f θ q))
    subst θ
    have hpq : p = q := (pullback.fst f (X.fromSpecStalk η.val)).isEmbedding.injective hv
    subst q
    rfl
  · intro ξ
    let η : genericPoints X := ⟨f ξ.val, genericPoint_map_flat f ξ⟩
    let l : Spec (U.presheaf.stalk ξ.val) ⟶ genericEtaleComponent f η :=
      pullback.lift (U.fromSpecStalk ξ.val) (Spec.map (f.stalkMap ξ.val))
        (Scheme.SpecMap_stalkMap_fromSpecStalk f).symm
    let p : genericEtaleComponent f η := l (IsLocalRing.closedPoint (U.presheaf.stalk ξ.val))
    refine ⟨⟨η, p⟩, Subtype.ext ?_⟩
    change (l ≫ pullback.fst f (X.fromSpecStalk η.val))
      (IsLocalRing.closedPoint (U.presheaf.stalk ξ.val)) = ξ.val
    rw [pullback.lift_fst]
    exact Scheme.fromSpecStalk_closedPoint

/-- Actual generic pullback points indexed by the genuine generic points of the test. -/
def genericEtaleIndexEquiv :
    (Σ η : genericPoints X, genericEtaleComponent f η) ≃ genericPoints U :=
  Equiv.ofBijective (genericEtaleIndexMap f) (genericEtaleIndexMap_bijective f)

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
