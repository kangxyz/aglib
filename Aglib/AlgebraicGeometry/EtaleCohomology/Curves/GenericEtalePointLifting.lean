/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinEtalePoints

/-!
# Generic points above generic points on arbitrary etale tests

The test need not be quasi-compact. An affine neighborhood reduces the claim
to the actual Artinian generic pullback; the original stalk spectra and maps
are retained throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

/-- An etale point above a generic point is generic, without quasi-compactness of the test. -/
theorem mem_genericPoints_of_etale_image {V U : Scheme.{u}} (f : V ⟶ U)
    [IsLocallyNoetherian U] [Etale f] (y : V) (hy : f y ∈ genericPoints U) :
    y ∈ genericPoints V := by
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨W, hW, hyW, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := V) (U := ⊤) (x := y) (by trivial)
  let : IsAffine W.toScheme := hW
  let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW.isCompact
  let : IsNoetherian W.toScheme := {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance }
  let r : W.toScheme ⟶ U := W.ι ≫ f
  let w : W.toScheme := ⟨y, hyW⟩
  let η : genericPoints U := ⟨f y, hy⟩
  let l : Spec (W.toScheme.presheaf.stalk w) ⟶ genericEtaleComponent r η :=
    pullback.lift (W.toScheme.fromSpecStalk w) (Spec.map (r.stalkMap w))
      (Scheme.SpecMap_stalkMap_fromSpecStalk r).symm
  let p : genericEtaleComponent r η :=
    l (IsLocalRing.closedPoint (W.toScheme.presheaf.stalk w))
  have hp : (pullback.fst r (U.fromSpecStalk η.val)) p = w := by
    change (l ≫ pullback.fst r (U.fromSpecStalk η.val))
      (IsLocalRing.closedPoint (W.toScheme.presheaf.stalk w)) = w
    have hl : l ≫ pullback.fst r (U.fromSpecStalk η.val) =
        W.toScheme.fromSpecStalk w := pullback.lift_fst _ _ _
    exact (congrArg (fun k : Spec (W.toScheme.presheaf.stalk w) ⟶ W.toScheme =>
      k (IsLocalRing.closedPoint (W.toScheme.presheaf.stalk w))) hl).trans
        Scheme.fromSpecStalk_closedPoint
  have hw : w ∈ genericPoints W.toScheme :=
    hp ▸ genericEtaleComponent_projection_generic r η p
  exact genericPoint_map_flat W.ι ⟨w, hw⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
