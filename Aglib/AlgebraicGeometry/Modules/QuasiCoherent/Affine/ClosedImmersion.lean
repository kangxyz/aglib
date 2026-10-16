/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.Algebra.Category.FGModuleCat.IdealClosedSupport
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Quasicoherent finite-type pushforward from affine closed subschemes

Relocated from
`Aglib/AlgebraicGeometry/Modules/Coherent/Pushforward/ClosedImmersion/IdealPushforward.lean` at
Aglib `451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `56d33b9c4b1d464c4226a9ce518ec9e8ea69f72b2503a1922f40214bab7f9bec`.
The statements retain their original universes, hypotheses and actual maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open ModuleCat

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Pushforward.ClosedImmersion.Ideal

open ModuleCat.FiniteLocalization.IdealClosedSupport

variable (R : CommRingCat.{u}) (I : Ideal R)

/-- The closed subscheme's affine coordinate ring. -/
abbrev closedRing : CommRingCat.{u} := CommRingCat.of (ClosedRing I)

/-- The actual closed immersion induced by the quotient map. -/
def closedMap : Spec (closedRing R I) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I)))

instance closedMap_isClosedImmersion : IsClosedImmersion (closedMap R I) := by
  unfold closedMap
  infer_instance

/-- Actual sheaf pushforward preserves the affine finite-type quasicoherent property. -/
theorem affineFiniteSheaf_pushforward {M : (Spec (closedRing R I)).Modules}
    (hM : affineFiniteSheaf (closedRing R I) M) :
    affineFiniteSheaf R ((Scheme.Modules.pushforward (closedMap R I)).obj M) := by
  have : M.IsQuasicoherent := hM.1
  refine ⟨Scheme.Modules.isQuasicoherent_pushforward _ M, ?_⟩
  let N : FGModuleCat (ClosedRing I) := ⟨moduleSpecΓFunctor.obj M, hM.2⟩
  have : Module.Finite R ((moduleSpecΓFunctor ⋙
      ModuleCat.restrictScalars (CommRingCat.ofHom (Ideal.Quotient.mk (I))).hom).obj M) :=
    ((closedRestriction I).obj N).property
  exact Module.Finite.equiv
    ((Scheme.Modules.pushforwardGlobalSectionsIso
      (CommRingCat.ofHom (Ideal.Quotient.mk (I)))).app M).symm.toLinearEquiv

/-- Actual closed pushforward preserves the all-affine-chart finite-type quasicoherent predicate. -/
theorem affineLocallyFiniteType_pushforward {M : (Spec (closedRing R I)).Modules}
    (hM : affineLocallyFiniteType (Spec (closedRing R I)) M) :
    affineLocallyFiniteType (Spec R) ((Scheme.Modules.pushforward (closedMap R I)).obj M) :=
  (affineLocallyFiniteType_spec_iff R _).mpr
    (affineFiniteSheaf_pushforward R I ((affineLocallyFiniteType_spec_iff (closedRing R I) M).mp
      hM))

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Pushforward.ClosedImmersion.Ideal
