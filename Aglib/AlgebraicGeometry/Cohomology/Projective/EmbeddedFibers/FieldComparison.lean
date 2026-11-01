/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.EmbeddedFibers.Core
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.FieldExtension.Comparison

/-! # Twisted fibre comparison from the original canonical map -/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι)

/-- The original twisted field-fibre comparison from invertibility of its canonical map. -/
theorem embeddedFiberTwistDim_fieldBaseChange_of_isIso {K K' : Type u} [Field K] [Field K']
    (k : Spec (.of K) ⟶ Spec (.of A)) (σ : K →+* K')
    (M : (pullback (i ≫ ProjectiveSpace.toSpec A ι) k).Modules) (n : ℤ)
    (q : ℕ)
    [IsIso (moduleCohomologyBaseChangeMap
      (pullback.snd (i ≫ ProjectiveSpace.toSpec A ι) k) σ
      (pulledTwist (pullback.fst (i ≫ ProjectiveSpace.toSpec A ι) k ≫ i) n M) q)] :
    embeddedFiberTwistDim i (Spec.map (CommRingCat.ofHom σ) ≫ k)
        ((Scheme.Modules.pullback (fieldExtensionBaseChange i k σ)).obj M) n q =
      embeddedFiberTwistDim i k M n q := by
  let f := i ≫ ProjectiveSpace.toSpec A ι
  let N := pulledTwist (pullback.fst f k ≫ i) n M
  have hdim :
      moduleCohomologyDimension
          (pullback.snd (pullback.snd f k) (Spec.map (CommRingCat.ofHom σ)))
          ((Scheme.Modules.pullback
            (pullback.fst (pullback.snd f k) (Spec.map (CommRingCat.ofHom σ)))).obj N) q =
        moduleCohomologyDimension (pullback.snd f k) N q :=
    moduleCohomology_finrank_fieldBaseChange_of_isIso (pullback.snd f k) σ N q
  unfold embeddedFiberTwistDim
  rw [← hdim, moduleCohomologyDimension_pullback_snd_pullback_snd]
  exact (moduleCohomologyDimension_congr _
    (pulledTwistPullbackIso _ _ _ (fieldExtensionBaseChange_fst_assoc i k σ i) n M) q).symm


end AlgebraicGeometry.Scheme.Cohomology
