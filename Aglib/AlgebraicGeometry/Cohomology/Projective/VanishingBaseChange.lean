/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.LocalBaseChange

/-!
# Residue-field base change when higher cohomology vanishes, over a local ring

Let `R` be a Noetherian local ring, `i : X ⟶ P^n_R` a closed immersion with `i ≫ toSpec = f`, and
`M` a coherent `𝒪_X`-module, relatively flat over `R`, whose cohomology vanishes in every positive
degree. Then the original residue-field cohomology base-change map
`κ ⊗_R H^q(X, M) ⟶ H^q(X_κ, M_κ)` is surjective in every degree `q`, and `H^0(X, M)` is a free
`R`-module. Over an arbitrary Noetherian ring, base change in every degree and projectivity of
`H^0` are proved in `Cohomology/Projective/VanishingProjective`.

This is the local form of the base-change step of Nitsure, *Construction of Hilbert and Quot
schemes*, arXiv:math/0504590v1, proof of Theorem 4.3: statements (B) and (C) for a flat family,
the input applied to each flat `F_{V_i}` in Nitsure's proof, p. 21, over an affine Noetherian
base (with Theorem 3.7, pp. 17–18), and of the exercise after Lemma 3.2, p. 15 (flatness gives
local freeness of the direct images `π_* F(r)` for `r ≫ 0`), once Serre vanishing supplies the
hypothesis for a twist `F(r)`. Nitsure's (B) and (C) for a coherent `F` that need not be flat are
not proved here. The proof is the descending induction on the degree with the
criteria of `Cohomology/Projective/LocalBaseChange`: the residue-field map is surjective above the
length of the finite-projective model, and if it is surjective in degree `q + 1`, where the
cohomology vanishes and so is free, it is surjective in degree `q`.

* `ProjectiveCohomologyModel.epi_residue_of_lt`: surjectivity of the residue-field map above `n`.
* `ProjectiveCohomologyModel.epi_residue_of_vanishing`: surjectivity in every degree.
* `moduleCohomology_zero_free_of_vanishing_of_projectiveEmbedding`: freeness of `H^0`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex Module AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {ι : Type u} {X : Scheme.{u}} {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- Above the length `n` of the finite-projective model, the original residue-field cohomology
base-change map is surjective: its target vanishes. -/
theorem ProjectiveCohomologyModel.epi_residue_of_lt
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M) (q : ℕ) (hq : n < q) :
    Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M q) := by
  let : D.complex.IsStrictlyLE (n : ℤ) := D.upperBound
  let K : CochainComplex (ModuleCat.{u} (IsLocalRing.ResidueField R)) ℤ :=
    ((ModuleCat.extendScalars (algebraMap R (IsLocalRing.ResidueField R))).mapHomologicalComplex
      (.up ℤ)).obj D.complex
  have : Epi (extendScalarsHomologyMap (algebraMap R (IsLocalRing.ResidueField R))
      D.complex (q : ℤ)) :=
    (K.isZero_of_isLE (n : ℤ) (q : ℤ) (by omega)).epi _
  exact (D.moduleCohomologyBaseChangeMap_epi_iff e hflat _ q).mpr this

/-- **Descending induction.** If the original cohomology vanishes in every positive degree, the
original residue-field cohomology base-change map is surjective in every degree. -/
theorem ProjectiveCohomologyModel.epi_residue_of_vanishing
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent]
    (e : ι ≃ Fin (n + 1)) (hflat : Scheme.Modules.relativeFlat f M)
    (hvan : ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)) (q : ℕ) :
    Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M q) := by
  suffices H : ∀ k q : ℕ, n + 1 ≤ q + k →
      Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M q) from
    H (n + 1) q (by omega)
  intro k
  induction k with
  | zero => exact fun q hq => D.epi_residue_of_lt e hflat q (by omega)
  | succ k ih =>
    intro q hq
    have : Epi (moduleCohomologyBaseChangeMap f (algebraMap R (IsLocalRing.ResidueField R)) M
        (q + 1)) := ih (q + 1) (by omega)
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let := moduleCohomologyModuleOfHom X α M (q + 1)
    have : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) (q + 1)) :=
      hvan (q + 1) (Nat.succ_ne_zero q)
    exact (D.free_moduleCohomology_iff_epi_residue_predecessor e hflat q).mp
      (Module.Free.of_subsingleton R _)

variable [IsNoetherianRing R]

/-- **Freeness of global sections in the vanishing case** (Nitsure, arXiv:math/0504590v1, the
vanishing-case step of the exercise after Lemma 3.2, p. 15, local form): over a Noetherian local
ring, if a coherent relatively flat coefficient on an actual projective embedding has no
cohomology in positive degrees, then its original degree-zero cohomology is a free module. -/
theorem moduleCohomology_zero_free_of_vanishing_of_projectiveEmbedding
    (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (hvan : ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  have := D.epi_residue_of_vanishing e hflat hvan 0
  exact D.free_moduleCohomology_zero_of_epi_residue e hflat

end AlgebraicGeometry.Scheme.Cohomology
