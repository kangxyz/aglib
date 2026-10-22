/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-! # Original pushforward base change to an adic completion

The comparison is the original geometric adjunction mate. Its invertibility
uses native flatness of Noetherian completion and degree-zero qcqs base change,
not faithful flatness or an inference from isomorphic reduction rings.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {B : Type u} [CommRing B] [IsNoetherianRing B]
  (J : Ideal B) {Y : Scheme.{u}}
  (p : Y ⟶ Spec (CommRingCat.of B)) [QuasiCompact p] [QuasiSeparated p]
  (G : Y.Modules) [G.IsQuasicoherent]

/-- Flat completion preserves the actual ordinary pushforward comparison. -/
theorem moduleBaseChangeMap_completion_isIso :
    IsIso (moduleBaseChangeMap p
      (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion J B)))) G) := by
  apply moduleBaseChangeMap_isIso_of_scalar_cohomology_zero
  exact Cohomology.moduleCohomologyBaseChangeMap_isIso_of_quasiSeparated p
    (algebraMap B (AdicCompletion J B))
    (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian J)) G 0

/-- The completed-base pushforward identification is the original mate itself. -/
def completionPushforwardBaseChangeIso :
    (pullback (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion J B))))).obj
        ((pushforward p).obj G) ≅
      (pushforward (CategoryTheory.Limits.pullback.snd p
        (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion J B)))))).obj
          ((pullback (CategoryTheory.Limits.pullback.fst p
            (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion J B)))))).obj G) := by
  let := moduleBaseChangeMap_completion_isIso J p G
  exact asIso (moduleBaseChangeMap p
    (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion J B)))) G)

/-- No choice of an unrelated pushforward isomorphism is made. -/
theorem completionPushforwardBaseChangeIso_hom :
    (completionPushforwardBaseChangeIso J p G).hom =
      moduleBaseChangeMap p
        (Spec.map (CommRingCat.ofHom (algebraMap B (AdicCompletion J B)))) G := rfl

end AlgebraicGeometry.Scheme.Modules
