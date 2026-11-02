/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback
public import Mathlib.Algebra.FiveLemma

/-! # Original pullback comparison through a short exact coefficient sequence

The native additive four lemma is applied to the actual long exact cohomology
sequence. Original connecting-map and coefficient-map pullback laws construct
the three squares. The source and target Ext worlds remain independent; no
cohomology groups are replaced or lifted into a new common model.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
  (f : S ⟶ X) (T : ShortComplex (AbelianSheaf.{u, u + 1} X)) (hT : T.ShortExact)

include hT

/-- Original successor-degree pullback is surjective by the actual short-exact
coefficient diagram and the native additive four lemma. -/
theorem cohomologyPullback_surjective_of_shortExact (q : ℕ)
    (h₀ : Function.Surjective (cohomologyPullback f T.X₃ q))
    (h₂ : Function.Surjective (cohomologyPullback f T.X₂ (q + 1)))
    (h₃ : Function.Injective (cohomologyPullback f T.X₃ (q + 1))) :
    Function.Surjective (cohomologyPullback f T.X₁ (q + 1)) := by
  let T' := T.map (inverseImage f)
  have hT' : T'.ShortExact := hT.map_of_exact (inverseImage f)
  apply AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    (Sheaf.H.δ hT q (q + 1) rfl) (Sheaf.H.map T.f (q + 1))
    (Sheaf.H.map T.g (q + 1))
    (Sheaf.H.δ hT' q (q + 1) rfl) (Sheaf.H.map T'.f (q + 1))
    (Sheaf.H.map T'.g (q + 1))
    (cohomologyPullback f T.X₃ q) (cohomologyPullback f T.X₁ (q + 1))
    (cohomologyPullback f T.X₂ (q + 1)) (cohomologyPullback f T.X₃ (q + 1))
    _ _ _ _ _ _ h₀ h₂ h₃
  · apply AddMonoidHom.ext
    intro a
    exact (connecting_cohomologyPullback f T hT q (q + 1) rfl a).symm
  · apply AddMonoidHom.ext
    intro a
    exact (cohomologyPullback_coefficientMap f T.f (q + 1) a).symm
  · apply AddMonoidHom.ext
    intro a
    exact (cohomologyPullback_coefficientMap f T.g (q + 1) a).symm
  · exact (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₂' hT (q + 1))
  · exact (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₁' hT' q (q + 1) rfl)
  · exact (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₂' hT' (q + 1))

/-- Degree zero/one specialization, with the unchanged original H0 and H1 maps.
No cover degree or trace splitting hypothesis is needed. -/
theorem h1Pullback_surjective_of_shortExact
    (h₀ : Function.Surjective (h0Pullback f T.X₃))
    (h₂ : Function.Surjective (h1Pullback f T.X₂))
    (h₃ : Function.Injective (h1Pullback f T.X₃)) :
    Function.Surjective (h1Pullback f T.X₁) :=
  cohomologyPullback_surjective_of_shortExact f T hT 0 h₀ h₂ h₃

end AlgebraicGeometry.Scheme.EtaleCohomology
