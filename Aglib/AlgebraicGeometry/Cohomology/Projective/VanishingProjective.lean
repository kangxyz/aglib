/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FiniteModel.BaseChangeCriterion
public import Aglib.Algebra.Homology.CochainComplex.ProjectiveCokernel

/-!
# Projective global sections and base change when higher cohomology vanishes

Let `R` be a Noetherian ring, `i : X ⟶ P^n_R` a closed immersion with `i ≫ toSpec = f`, and `M` a
coherent `𝒪_X`-module, relatively flat over `R`, whose cohomology vanishes in every positive
degree. Then `H^0(X, M)` is a projective `R`-module and the original cohomology base-change map
`B ⊗_R H^q(X, M) ⟶ H^q(X_B, M_B)` is an isomorphism for every ring map `R →+* B` and every `q`.
No locality of `R` is assumed.

This is the base-change step of Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, proof of Theorem 4.3: statements (B) and (C) for a flat family, the input
applied to each flat `F_{V_i}` in Nitsure's proof, p. 21, over an affine Noetherian base; and the
vanishing-case step of the exercise after Lemma 3.2, p. 15 (`π_* F(r)` is locally free for
`r ≫ 0` when `F` is flat), once Serre vanishing supplies the hypothesis for a twist `F(r)`.
Nitsure's (B) and (C) themselves concern a coherent `F` that need not be flat; they are not proved
here. The positive-degree cohomology then also vanishes after every base change
(`subsingleton_moduleCohomology_pullback_of_vanishing_of_projectiveEmbedding`).

The proof is algebra on the finite-projective model `K` of the cohomology
(`ProjectiveCohomologyModel`), a complex of finite projective modules in degrees `[0, n]`. If
`H^q(K) = 0` for `q ≥ 1`, every cokernel `coker(d^q)`, `q ≥ 0`, is projective
(`CochainComplex.projective_cokernel_d_of_vanishing`, in
`Algebra/Homology/CochainComplex/ProjectiveCokernel`). Projectivity of `coker(d^q)` gives base
change in degree `q` (`CochainComplex.extendScalarsHomologyMap_isIso_of_vanishing`) and, in
degree `0`, projectivity of `H^0` (`CochainComplex.projective_homology_zero_of_vanishing`).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R]
    {ι : Type u} {X : Scheme.{u}} {i : X ⟶ ProjectiveSpace R ι} [IsClosedImmersion i]
    {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {n : ℕ}

/-- Vanishing of original cohomology in a degree is vanishing of the model homology. -/
theorem ProjectiveCohomologyModel.isZero_homology_of_subsingleton
    (D : ProjectiveCohomologyModel R ι i f M n) [M.IsQuasicoherent] (e : ι ≃ Fin (n + 1))
    (q : ℕ) (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)) :
    IsZero (D.complex.homology (q : ℤ)) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X α M q
  have : Subsingleton (D.complex.homology (q : ℤ)) :=
    (D.cohomologyLinearEquiv e q).toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

variable [IsNoetherianRing R]

/-- **Cohomology and base change in the vanishing case** (Nitsure, arXiv:math/0504590v1, proof of
Theorem 4.3, (B) and (C) for a flat family, the input applied to each flat `F_{V_i}`, p. 21, over
an affine Noetherian base): if a coherent relatively flat
coefficient on an actual projective embedding over a Noetherian ring has no cohomology in positive
degrees, then the original cohomology base-change map `B ⊗_R H^q(X, M) ⟶ H^q(X_B, M_B)` is an
isomorphism for every ring map `σ : R →+* B` and every degree `q`. -/
theorem moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding
    (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (hvan : ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q))
    (q : ℕ) {B : Type u} [CommRing B] (σ : R →+* B) :
    IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  let : D.complex.IsStrictlyLE (n : ℤ) := D.upperBound
  exact (D.moduleCohomologyBaseChangeMap_isIso_iff e hflat σ q).mpr
    (D.complex.extendScalarsHomologyMap_isIso_of_vanishing n
      (fun q hq => D.isZero_homology_of_subsingleton e q (hvan q hq)) σ q)

/-- **Projective global sections in the vanishing case**: if a coherent relatively flat
coefficient on an actual projective embedding over a Noetherian ring has no cohomology in positive
degrees, then its original degree-zero cohomology is a projective module. This is the
vanishing-case step of the exercise after Nitsure, arXiv:math/0504590v1, Lemma 3.2, p. 15, over
an affine Noetherian base; the exercise itself is
`exists_twist_baseChange_isIso_and_projective_of_relativeFlat`. With finite generation
(`moduleCohomology_finite_of_projectiveEmbedding`) the module is finite projective, so its
associated sheaf on `Spec R` is locally free. -/
theorem moduleCohomology_zero_projective_of_vanishing_of_projectiveEmbedding
    (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (hvan : ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    Module.Projective R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) := by
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  let D := projectiveCohomologyModelOfEmbedding R ι i f M n e hf hM hflat
  let (j : ℤ) : Module.Projective R (D.complex.X j) := D.projective_X j
  let : D.complex.IsStrictlyGE 0 := D.lowerBound
  let : D.complex.IsStrictlyLE (n : ℤ) := D.upperBound
  have h := D.complex.projective_homology_zero_of_vanishing n
    (fun q hq => D.isZero_homology_of_subsingleton e q (hvan q hq))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X α M 0
  exact Module.Projective.of_equiv (D.cohomologyLinearEquiv e 0)

/-- **Vanishing after every base change** (Nitsure, arXiv:math/0504590v1, proof of Theorem 4.3,
(B) for a flat family, the input applied to each flat `F_{V_i}`, p. 21, over an affine Noetherian
base): under the same hypotheses, the cohomology of the
pulled-back coefficient on `X ×_{Spec R} Spec B` vanishes in every positive degree, for every ring
map `σ : R →+* B`; for residue fields these are the fibres. -/
theorem subsingleton_moduleCohomology_pullback_of_vanishing_of_projectiveEmbedding
    (e : ι ≃ Fin (n + 1)) (hf : i ≫ toSpec R ι = f)
    (hM : affineLocallyFiniteType X M) (hflat : Scheme.Modules.relativeFlat f M)
    (hvan : ∀ q : ℕ, q ≠ 0 → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q))
    (q : ℕ) (hq : q ≠ 0) {B : Type u} [CommRing B] (σ : R →+* B) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (pullback f (Spec.map (CommRingCat.ofHom σ)))
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) q) := by
  have hiso := moduleCohomologyBaseChangeMap_isIso_of_vanishing_of_projectiveEmbedding
    e hf hM hflat hvan q σ
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X α M q
  have : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := hvan q hq
  have hz : IsZero ((ModuleCat.extendScalars σ).obj
      (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) q))) :=
    (ModuleCat.extendScalars σ).map_isZero (ModuleCat.isZero_of_subsingleton _)
  exact ModuleCat.subsingleton_of_isZero
    (hz.of_iso (asIso (moduleCohomologyBaseChangeMap f σ M q)).symm)

end AlgebraicGeometry.Scheme.Cohomology
