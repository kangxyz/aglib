/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.SerreVanishing
public import Aglib.AlgebraicGeometry.Cohomology.Projective.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor

/-!
# Serre vanishing through an actual closed projective embedding

The tensor object, projective-embedding cohomology comparison, and projection
formula are the original native constructions. One bound controls every
positive cohomology degree. The base is any Noetherian commutative ring; the
actual finite coordinate labeling is retained and no relative flatness is needed.

This is the single generic implementation formerly at the start of
Surfaces/Contraction/ProjectiveSections. Its old names are transparent adapters.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {ι : Type u} {X : Scheme.{u}}
  (p : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion p]

/-- The actual tensor twist pulled back from the specified projective embedding. -/
abbrev embeddedTensorTwist (d : ℤ) (F : X.Modules) : X.Modules :=
  (moduleTensorLeftFunctor X ((Scheme.Modules.pullback p).obj
    (twistingSheaf A ι d))).obj F

/-- Serre vanishing on a genuine closed projective subscheme, with the original
pullback tensor object and native sheaf cohomology. No relative flatness is needed. -/
theorem embeddedTensorTwist_serreVanishing (r : ℕ) (e : ι ≃ Fin (r + 1))
    (F : X.Modules) (hF : affineLocallyFiniteType X F) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ q : ℕ, q ≠ 0 →
      Subsingleton (Sheaf.H.{u + 1} (Cohomology.moduleAddSheaf X
        (embeddedTensorTwist p d F)) q) := by
  let : Finite ι := Finite.of_equiv _ e.symm
  let : F.IsQuasicoherent :=
    quasicoherent_of_affineCharts F (fun R j _ => (hF R j).1)
  have hPF := Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward p hF
  let : ((Scheme.Modules.pushforward p).obj F).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun R j _ => (hPF R j).1)
  obtain ⟨B, hB⟩ := Cohomology.projectiveSerreVanishing A ι r e
    ((Scheme.Modules.pushforward p).obj F) hPF
  refine ⟨B, fun d hd q hq => ?_⟩
  let : (embeddedTensorTwist p d F).IsQuasicoherent :=
    isQuasicoherent_moduleTensorLeftFunctor _ _
  let : ((Scheme.Modules.pushforward p).obj (embeddedTensorTwist p d F)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom p _
  let := Cohomology.moduleCohomology_subsingleton_of_iso
    (closedImmersionProjectionFormulaIso p (twistingSheaf A ι d) F) q (hB d hd q hq)
  exact (Cohomology.projectiveEmbeddingCohomologyLinearEquiv A ι p
    (embeddedTensorTwist p d F) q).surjective.subsingleton

end AlgebraicGeometry.Scheme.Cohomology
