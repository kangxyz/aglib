/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.SerreVanishing
public import Aglib.AlgebraicGeometry.Cohomology.Projective.VanishingBaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Projective.VanishingProjective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Flat

/-!
# Direct images of large twists of a flat family

Let `R` be a Noetherian ring and `F` a coherent module on `P^n_R`, relatively flat over `R`. For all
sufficiently large `d`, the twist `F(d) = 𝒪(d) ⊗ F` has projective global sections
`H^0(P^n_R, F(d))` (free when `R` is local), and its original cohomology base-change maps
`B' ⊗_R H^q(P^n_R, F(d)) ⟶ H^q((P^n_R)_{B'}, F(d)_{B'})` are isomorphisms for every ring map
`R →+* B'` and every degree `q`. The bound `B` is Serre's bound for `F`. Here `(P^n_R)_{B'}` is
the fibre product `P^n_R ×_{Spec R} Spec B'` and `F(d)_{B'}` the pullback of `F(d)` along its first
projection; no identification with `𝒪_{B'}(d) ⊗ F_{B'}` on `P^n_{B'}` is used.

This is the exercise after Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Lemma 3.2, p. 15 (if `F` is flat over `S`, then `π_* F(r)` is locally free
for all `r ≫ 0`), together with statements (B) and (C) of the proof of Theorem 4.3 for a flat
family, the input applied to each flat `F_{V_i}` in Nitsure's proof, p. 21, over an affine
Noetherian base `S = Spec R`. Nitsure's (B) and (C) for a coherent `F` that need not be flat are
not proved here. Twists of a relatively flat module are relatively flat by
`ProjectiveSpace.twistingTensor_relativeFlat`.

* `exists_twist_baseChange_isIso_and_projective_of_relativeFlat`: the statement above;
* `exists_twist_baseChange_isIso_and_free_of_relativeFlat`: the same over a local ring, with free
  global sections;
* `exists_twist_subsingleton_cohomology_pullback_of_relativeFlat`: for `d ≥ B`, the positive-degree
  cohomology of `F(d)_{B'}` vanishes for every ring map `R →+* B'` (Nitsure, (B) for a flat family,
  p. 21, on the fibres).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- **Large twists of a flat family** (Nitsure, arXiv:math/0504590v1, exercise after Lemma 3.2,
p. 15, and proof of Theorem 4.3, (B) and (C) for a flat family, the input applied to each flat
`F_{V_i}`, p. 21, over an affine Noetherian base): for `F`
coherent on `P^n_R` and relatively flat over the Noetherian ring `R`, there is a bound `B` such that
for every `d ≥ B` the cohomology base-change maps of `F(d)` are isomorphisms for every ring map and
every degree, and `H^0(P^n_R, F(d))` is a projective `R`-module. -/
theorem exists_twist_baseChange_isIso_and_projective_of_relativeFlat {R : Type u} [CommRing R]
    [IsNoetherianRing R] {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    (hflat : relativeFlat (toSpec R ι) F) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      (∀ (q : ℕ) (B' : Type u) [CommRing B'] (σ : R →+* B'),
        IsIso (moduleCohomologyBaseChangeMap (toSpec R ι) σ
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) q)) ∧
      (let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) 0
       Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)) 0)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨B, hB⟩ := projectiveSerreVanishing R ι n e F hF
  refine ⟨B, fun d hd => ⟨fun q B' _ σ => ?_, ?_⟩⟩
  · exact moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding
      (i := 𝟙 _) e (Category.id_comp _) (twistingTensor_affineLocallyFiniteType R ι d F hF)
      (twistingTensor_relativeFlat _ F hflat d) (hB d hd) q σ
  · exact moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding
      (i := 𝟙 _) e (Category.id_comp _) (twistingTensor_affineLocallyFiniteType R ι d F hF)
      (twistingTensor_relativeFlat _ F hflat d) (hB d hd)

/-- **Large twists of a flat family over a Noetherian local ring**: as
`exists_twist_baseChange_isIso_and_projective_of_relativeFlat`, with free global sections. -/
theorem exists_twist_baseChange_isIso_and_free_of_relativeFlat {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    (hflat : relativeFlat (toSpec R ι) F) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      (∀ (q : ℕ) (B' : Type u) [CommRing B'] (σ : R →+* B'),
        IsIso (moduleCohomologyBaseChangeMap (toSpec R ι) σ
          ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) q)) ∧
      (let α := (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
       letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) 0
       Module.Free R (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι)
         ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F)) 0)) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨B, hB⟩ := projectiveSerreVanishing R ι n e F hF
  refine ⟨B, fun d hd => ⟨fun q B' _ σ => ?_, ?_⟩⟩
  · exact moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding
      (i := 𝟙 _) e (Category.id_comp _) (twistingTensor_affineLocallyFiniteType R ι d F hF)
      (twistingTensor_relativeFlat _ F hflat d) (hB d hd) q σ
  · exact moduleCohomology_zero_free_of_vanishing_of_projectiveEmbedding
      (i := 𝟙 _) e (Category.id_comp _) (twistingTensor_affineLocallyFiniteType R ι d F hF)
      (twistingTensor_relativeFlat _ F hflat d) (hB d hd)

/-- **Uniform vanishing on all base changes** (Nitsure, arXiv:math/0504590v1, proof of
Theorem 4.3, (B) for a flat family, the input applied to each flat `F_{V_i}`, p. 21, over an affine
Noetherian base): for `F` coherent on `P^n_R` and
relatively flat over the Noetherian ring `R`, there is a bound `B` such that for every `d ≥ B`,
every `q ≥ 1` and every ring map `σ : R →+* B'`, the cohomology `H^q` of the pullback of `F(d)` to
`P^n_R ×_{Spec R} Spec B'` vanishes. -/
theorem exists_twist_subsingleton_cohomology_pullback_of_relativeFlat {R : Type u} [CommRing R]
    [IsNoetherianRing R] {ι : Type u} (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace R ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace R ι) F)
    (hflat : relativeFlat (toSpec R ι) F) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ q : ℕ, q ≠ 0 → ∀ (B' : Type u) [CommRing B'] (σ : R →+* B'),
      Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf (pullback (toSpec R ι) (Spec.map (CommRingCat.ofHom σ)))
          ((Scheme.Modules.pullback
              (pullback.fst (toSpec R ι) (Spec.map (CommRingCat.ofHom σ)))).obj
            ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F))) q) := by
  have : Finite ι := Finite.of_equiv _ e.symm
  obtain ⟨B, hB⟩ := projectiveSerreVanishing R ι n e F hF
  exact ⟨B, fun d hd q hq B' _ σ =>
    subsingleton_moduleCohomology_pullback_of_vanishing_of_projectiveEmbedding
      (i := 𝟙 _) e (Category.id_comp _) (twistingTensor_affineLocallyFiniteType R ι d F hF)
      (twistingTensor_relativeFlat _ F hflat d) (hB d hd) q hq σ⟩

end AlgebraicGeometry.Scheme.Cohomology
