/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Projective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence

/-!
# Twisting the coefficient on the fibre of a projective embedding

Let `i : X ⟶ P^N_A` be a closed immersion, `k : Spec K ⟶ Spec A` a field point and `M` a coherent
module on `X_K = X ×_{Spec A} Spec K`. Twisting the coefficient shifts the twist degree:
`h^q(X_K, O(n) ⊗ (O(m) ⊗ M)) = h^q(X_K, O(n + m) ⊗ M)` (`embeddedFiberTwistDim_pulledTwist`), and
likewise for the Euler characteristic (`embeddedFiberTwistEulerChar_pulledTwist`). Both sides are
computed on `P^N_K` (`embeddedFiberTwistDim_eq_projectiveCohomologyDim`), where the projection
formula of the fibre embedding `ι` gives `ι_*(O(m) ⊗ M) ≅ O(m) ⊗ ι_* M`
(`closedImmersionProjectionFormulaIso`) and the twisting sheaves compose,
`O(n) ⊗ (O(m) ⊗ F) ≅ O(n + m) ⊗ F` (`twistingTensorCompIso`).

These are the fibre identities behind Kleiman's twist isomorphism `Pic^φ_m ≅ Pic^{φ₀}_0`,
`L ↦ L(m)` (*The Picard scheme*, arXiv:math/0504020v1, pp. 29–30), with `φ₀(n) = φ(n - m)`; the
printed `φ₀(n) = φ(m + n)` is a misprint (Picard plan, Representability step 2).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}} (i : X ⟶ ProjectiveSpace A ι)
  [IsClosedImmersion i] {K : Type u} [Field K] (k : Spec (.of K) ⟶ Spec (.of A))

/-- The twist of a coherent module on the fibre is coherent. -/
theorem affineLocallyFiniteType_pulledTwist {Y : Scheme.{u}} (h : Y ⟶ ProjectiveSpace A ι)
    (m : ℤ) {M : Y.Modules} (hM : affineLocallyFiniteType Y M) :
    affineLocallyFiniteType Y (pulledTwist h m M) :=
  affineLocallyFiniteType_tensor _ _
    (affineLocallyFiniteType_of_isLocallyRankOne (isLocallyRankOne_pulledTwistingSheaf h m)) hM

/-- **Twisting the coefficient shifts the twist**: for a coherent `M` on `X_K`,
`h^q(X_K, O(n) ⊗ (O(m) ⊗ M)) = h^q(X_K, O(n + m) ⊗ M)`. -/
theorem embeddedFiberTwistDim_pulledTwist (M : (pullback (i ≫ toSpec A ι) k).Modules)
    (hM : affineLocallyFiniteType (pullback (i ≫ toSpec A ι) k) M) (m n : ℤ) (q : ℕ) :
    embeddedFiberTwistDim i k (pulledTwist (pullback.fst (i ≫ toSpec A ι) k ≫ i) m M) n q =
      embeddedFiberTwistDim i k M (n + m) q := by
  rw [embeddedFiberTwistDim_eq_projectiveCohomologyDim i k _
      (affineLocallyFiniteType_pulledTwist _ m hM) n q,
    embeddedFiberTwistDim_eq_projectiveCohomologyDim i k M hM (n + m) q]
  let e₀ : pulledTwist (pullback.fst (i ≫ toSpec A ι) k ≫ i) m M ≅
      (moduleTensorLeftFunctor (pullback (i ≫ toSpec A ι) k)
        ((Scheme.Modules.pullback (embeddedFiberι i k)).obj (twistingSheaf K ι m))).obj M :=
    (moduleTensorRightFunctor _ M).mapIso (embeddedFiberTwistingIso i k m)
  let e : (Scheme.Modules.pushforward (embeddedFiberι i k)).obj
        (pulledTwist (pullback.fst (i ≫ toSpec A ι) k ≫ i) m M) ≅
      (moduleTensorLeftFunctor (ProjectiveSpace K ι) (twistingSheaf K ι m)).obj
        ((Scheme.Modules.pushforward (embeddedFiberι i k)).obj M) :=
    (Scheme.Modules.pushforward (embeddedFiberι i k)).mapIso e₀ ≪≫
      (closedImmersionProjectionFormulaIso (embeddedFiberι i k) (twistingSheaf K ι m) M).symm
  exact projectiveCohomologyDim_congr K ι
    ((moduleTensorLeftFunctor (ProjectiveSpace K ι) (twistingSheaf K ι n)).mapIso e ≪≫
      (twistingTensorCompIso K ι n m).app
        ((Scheme.Modules.pushforward (embeddedFiberι i k)).obj M)) q

/-- **Twisting the coefficient shifts the twist**, for Euler characteristics:
`χ(X_K, O(n) ⊗ (O(m) ⊗ M)) = χ(X_K, O(n + m) ⊗ M)`. -/
theorem embeddedFiberTwistEulerChar_pulledTwist (M : (pullback (i ≫ toSpec A ι) k).Modules)
    (hM : affineLocallyFiniteType (pullback (i ≫ toSpec A ι) k) M) (m n : ℤ) :
    embeddedFiberTwistEulerChar i k (pulledTwist (pullback.fst (i ≫ toSpec A ι) k ≫ i) m M) n =
      embeddedFiberTwistEulerChar i k M (n + m) := by
  rw [embeddedFiberTwistEulerChar_eq, embeddedFiberTwistEulerChar_eq]
  congr 1
  funext q
  rw [embeddedFiberTwistDim_pulledTwist i k M hM m n q]

end AlgebraicGeometry.Scheme.Cohomology
