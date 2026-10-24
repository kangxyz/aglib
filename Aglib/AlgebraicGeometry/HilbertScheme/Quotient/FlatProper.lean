/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Flat proper quotients over an affine base

Let `A` be a ring, `πZ : Z ⟶ Spec A` and `p₁, p₂ : R ⟶ Z`. A **flat proper quotient** of `Z` by
`(p₁, p₂)` (`FlatProperQuotient πZ p₁ p₂`) is an H-quasi-projective scheme `πQ : Q ⟶ Spec A`
(`IsHQuasiProjective`, a quasi-compact immersion into some `P(ι)_A`) with a flat, surjective and
proper morphism `q : Z ⟶ Q` over `Spec A` such that the square `(p₁, p₂, q, q)` is cartesian,
that is, `R ≅ Z ×_Q Z` through `(p₁, p₂)`. This is the conclusion of Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, Theorem 6.8 (p. 33: "`Q` is quasi-projective over
`S`, the morphism `X → Q` is faithfully flat and projective, and the induced morphism
`(f₁, f₂) : R → X ×_Q X` is an isomorphism") over `S = Spec A`, with "projective" weakened to
"proper"; compare Theorem 6.9 (p. 36). The existence statement for a schematic equivalence
relation is proved from a Hilbert datum in
`Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Effective`.

Consequences of the fields:

* `FlatProperQuotient.quasiCompact`: `q` is quasi-compact (it is proper).
* `FlatProperQuotient.isLocallyNoetherian`, `FlatProperQuotient.locallyOfFinitePresentation`: for
  `A` Noetherian, `Q` is locally Noetherian (`IsHQuasiProjective.isLocallyNoetherian`) and `q`,
  locally of finite type into a locally Noetherian scheme, is locally of finite presentation.
* `FlatProperQuotient.isSeparated`, `FlatProperQuotient.locallyOfFiniteType`: `πQ` is separated
  and locally of finite type.
* `FlatProperQuotient.effectiveEpi` and `FlatProperQuotient.isColimitCofork`: `q` is an effective
  epimorphism (Mathlib's instance for flat, surjective, quasi-compact morphisms; Nitsure,
  Lemma 6.7(1), p. 32), hence a coequalizer of `p₁, p₂` in the category of schemes
  (`CategoryTheory.isColimitCoforkOfEffectiveEpi` with the kernel pair `R`). Nitsure's schematic
  quotient (p. 31) is a coequalizer among `S`-schemes; that follows, since the factorization of an
  `S`-morphism through the epimorphism `q` is again over `S`.
* `FlatProperQuotient.singleton_mem_fppfPrecoverage`: for `A` Noetherian, `{q}` is an fppf covering
  of `Q`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {Z R : Scheme.{u}}

/-- **A flat proper quotient** of `Z` by `p₁, p₂ : R ⟶ Z` over `Spec A` (Nitsure,
arXiv:math/0504590v1, Theorem 6.8, p. 33, with "projective" weakened to "proper"): an
H-quasi-projective `Q` over `Spec A` with a flat, surjective, proper `q : Z ⟶ Q` over `Spec A`
whose kernel pair is `R` through `p₁, p₂`. -/
structure FlatProperQuotient (πZ : Z ⟶ Spec (.of A)) (p₁ p₂ : R ⟶ Z) where
  /-- The quotient scheme. -/
  Q : Scheme.{u}
  /-- The structure morphism of the quotient. -/
  πQ : Q ⟶ Spec (.of A)
  /-- The quotient morphism. -/
  q : Z ⟶ Q
  /-- The quotient morphism is a morphism over `Spec A`. -/
  fac : q ≫ πQ = πZ
  /-- The quotient is H-quasi-projective over `Spec A`. -/
  isHQuasiProjective : IsHQuasiProjective πQ
  /-- The quotient morphism is flat. -/
  flat : Flat q
  /-- The quotient morphism is surjective. -/
  surjective : Surjective q
  /-- The quotient morphism is proper. -/
  isProper : IsProper q
  /-- The quotient is effective: `R` is the fibre product `Z ×_Q Z` through `p₁, p₂`. -/
  isPullback : IsPullback p₁ p₂ q q

namespace FlatProperQuotient

variable {πZ : Z ⟶ Spec (.of A)} {p₁ p₂ : R ⟶ Z} (𝔮 : FlatProperQuotient πZ p₁ p₂)

instance isHQuasiProjective_πQ : IsHQuasiProjective 𝔮.πQ :=
  𝔮.isHQuasiProjective

instance flat_q : Flat 𝔮.q :=
  𝔮.flat

instance surjective_q : Surjective 𝔮.q :=
  𝔮.surjective

instance isProper_q : IsProper 𝔮.q :=
  𝔮.isProper

/-- The quotient morphism is quasi-compact. -/
theorem quasiCompact : QuasiCompact 𝔮.q :=
  inferInstance

/-- Over a Noetherian ring, the quotient is locally Noetherian. -/
instance isLocallyNoetherian [IsNoetherianRing A] : IsLocallyNoetherian 𝔮.Q :=
  IsHQuasiProjective.isLocallyNoetherian 𝔮.πQ

/-- Over a Noetherian ring, the quotient morphism is locally of finite presentation. -/
theorem locallyOfFinitePresentation [IsNoetherianRing A] : LocallyOfFinitePresentation 𝔮.q :=
  inferInstance

/-- The quotient is separated over `Spec A`. -/
theorem isSeparated : IsSeparated 𝔮.πQ :=
  inferInstance

/-- The quotient is locally of finite type over `Spec A`. -/
theorem locallyOfFiniteType : LocallyOfFiniteType 𝔮.πQ :=
  inferInstance

/-- **The quotient morphism is an effective epimorphism** (Nitsure, arXiv:math/0504590v1,
Lemma 6.7(1), p. 32): it is flat, surjective and quasi-compact. -/
theorem effectiveEpi : EffectiveEpi 𝔮.q :=
  inferInstance

/-- **The quotient morphism is a coequalizer of `p₁, p₂`** (Nitsure, arXiv:math/0504590v1,
Theorem 6.8, p. 35, (iii)): an effective epimorphism is the coequalizer of its kernel pair, which
is `R`. -/
def isColimitCofork : IsColimit (Cofork.ofπ 𝔮.q 𝔮.isPullback.w) :=
  isColimitCoforkOfEffectiveEpi 𝔮.q 𝔮.isPullback.cone 𝔮.isPullback.isLimit

/-- **The quotient morphism is an fppf covering**: over a Noetherian ring, `{q}` is a covering of
`Q` in the fppf precoverage. -/
theorem singleton_mem_fppfPrecoverage [IsNoetherianRing A] :
    Presieve.singleton 𝔮.q ∈ Scheme.fppfPrecoverage 𝔮.Q :=
  have := 𝔮.locallyOfFinitePresentation
  Scheme.Hom.singleton_mem_fppfPrecoverage 𝔮.q

end FlatProperQuotient

end AlgebraicGeometry
