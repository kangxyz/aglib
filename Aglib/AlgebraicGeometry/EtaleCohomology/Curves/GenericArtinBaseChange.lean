/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtinEtalePullback

/-!
# The actual generic map and its whole etale base change

The canonical generic map is flat and surjective on stalk maps, as checked
on its original component open cover. These properties persist under actual
base change, giving original projection stalk isomorphisms. Quasi-compact
etale tests give Artinian whole pullbacks, not reduced generic fibres.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable (X : Scheme.{u})

/-- The original generic map is flat, without a finite-type premise. -/
theorem genericArtinMap_flat : Flat (genericArtinMap X) := by
  let : IsZariskiLocalAtSource (@AlgebraicGeometry.Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  change AlgebraicGeometry.Flat (Sigma.desc (fun η : genericPoints X => X.fromSpecStalk η.val))
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat)
    (sigmaOpenCover (genericArtinComponent X))]
  intro η
  change genericPoints X at η
  change Flat (Sigma.ι (genericArtinComponent X) η ≫ genericArtinMap X)
  rw [genericArtinMap_component]
  exact Scheme.fromSpecStalk_flat X η.val

/-- Its original local ring maps are surjective, checked on the actual component cover. -/
theorem genericArtinMap_surjectiveOnStalks : SurjectiveOnStalks (genericArtinMap X) := by
  change SurjectiveOnStalks (Sigma.desc (fun η : genericPoints X => X.fromSpecStalk η.val))
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SurjectiveOnStalks)
    (sigmaOpenCover (genericArtinComponent X))]
  intro η
  change genericPoints X at η
  change SurjectiveOnStalks (Sigma.ι (genericArtinComponent X) η ≫ genericArtinMap X)
  rw [genericArtinMap_component]
  infer_instance

variable {X} {U : Scheme.{u}} (f : U ⟶ X)

/-- Every actual whole-base-change projection induces its own stalk isomorphism. -/
theorem genericArtinBaseChange_stalkMap_isIso (p : (pullback f (genericArtinMap X) : Scheme.{u})) :
    IsIso ((pullback.fst f (genericArtinMap X)).stalkMap p) := by
  let : Flat (genericArtinMap X) := genericArtinMap_flat X
  let : SurjectiveOnStalks (genericArtinMap X) := genericArtinMap_surjectiveOnStalks X
  let : SurjectiveOnStalks (pullback.fst f (genericArtinMap X)) :=
    SurjectiveOnStalks.stableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (genericArtinMap X)).flip
      (genericArtinMap_surjectiveOnStalks X)
  exact Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ p

/-- The whole pullback on a quasi-compact etale test is an actual Artinian scheme. -/
theorem genericArtinBaseChange_isArtinian [IsNoetherian X] [Etale f] [QuasiCompact f] :
    IsArtinianScheme (pullback f (genericArtinMap X)) := {
  toIsLocallyArtinian := IsLocallyArtinian.of_locallyQuasiFinite
    (pullback.snd f (genericArtinMap X))
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
    (pullback.snd f (genericArtinMap X)) }

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
