/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Affine-base localization of a concrete relative quasi-affine factorization

An immersion into an affine morphism becomes an immersion into an affine
scheme after an affine base change. Quasi-compactness of the composite makes
the actual pullback source quasi-compact, hence quasi-affine. Neither local
finite type nor affineness of the original base is needed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact composite of an immersion and an affine morphism has
quasi-affine source after any base change from an affine scheme. -/
theorem IsQuasiAffine.pullback_of_immersion_affine {Y P X Z : Scheme.{u}}
    (e : Y ⟶ P) (a : P ⟶ X) (q : Z ⟶ X)
    [IsImmersion e] [IsAffineHom a] [QuasiCompact (e ≫ a)] [IsAffine Z] :
    (pullback (e ≫ a) q).IsQuasiAffine := by
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd (e ≫ a) q)
  let m : pullback (e ≫ a) q ⟶ pullback a q :=
    (pullbackRightPullbackFstIso a q e).inv ≫ pullback.snd e (pullback.fst a q)
  have : IsImmersion m := inferInstance
  exact IsQuasiAffine.of_isImmersion m

end AlgebraicGeometry.Scheme
