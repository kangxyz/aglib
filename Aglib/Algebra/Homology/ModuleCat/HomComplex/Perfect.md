# Signed evaluation on finite-projective restrictions

[Perfect.lean](Perfect.lean) proves invertibility of the original signed
A-derived evaluation from an actual bounded finite-projective R-model of
the original scalar restriction. The maps are the evaluation from
[Evaluation.lean](Evaluation.lean), its localization from
[Derived.lean](Derived.lean), and the actual evaluation-at-one comparison
from [Coinduction.lean](Coinduction.lean).

The abstract contract uses commutative rings R and A and an actual ring
map `sigma : R →+* A`. It keeps their universes independent. In the common
module-carrier universe, W is an actual R-module with a specified linear
equivalence `W ≃ₗ[R] R`; an appropriate ULift of R supplies such a copy.
Let `S = singleFunctor 0 W`. The coefficient data are an actual
quasi-isomorphism `u : S → I` and K-injectivity of I. The derived endpoint
also uses K-injectivity of the actual coinduced complex `J = G(I)`.

For an actual A-complex K, the model data are an actual R-complex P,
integers a and b with `P.IsStrictlyGE a` and `P.IsStrictlyLE b`, finite
projectivity of every original P term, and an actual quasi-isomorphism
`q : P → Res(K)`. These are ordinary model data, with no supplied
evaluation-isomorphism or duality predicate. The endpoints are:

- `evaluation_coinduced_quasiIso_of_model`: the genuine A-linear chain
  evaluation is a quasi-isomorphism;
- `derivedEvaluation_app_Q_isIso_of_model`: its original derived
  component at `Q_A(K)` is invertible;
- `derivedEvaluation_isIso_of_model`: the original component at any
  actual derived object T is invertible through a displayed representative
  isomorphism `Q_A(K) ≅ T`.

The proof first constructs actual target postcomposition on the native
Hom cochains and its `ShortComplex.LeftHomologyMapData`. K-projective
`Qh_map_bijective` identifies this specific cohomology map with
postcomposition by the original shifted localized target map. This gives
`postcomp_quasiIso` for a K-projective source, complementing the existing
K-injective precomposition theorem.

Native `Cochain.toSingleEquiv`, upgraded with the original R-scalars,
identifies `Hom_R(P,S)^n` with the dual of `P^(-n)`. Applying this
comparison twice sends the actual evaluation in degree p to
`(p*(-p)).negOnePow` times `Module.Dual.eval`. Native finite-projective
reflexivity proves this component bijective. The original evaluation is
already a chain map, so its single-coefficient version is a chain
isomorphism. The single dual has finite-projective terms, and the lower
bound a of P gives it upper bound `-a`.

Writing `Pdual = Hom_R(P,S)`, the original augmentation u induces

`alpha : Pdual → Hom_R(P,I)`,

`beta : Hom_R(Pdual,S) → Hom_R(Pdual,I)`,

`gamma : Hom_R(Hom_R(P,I),I) → Hom_R(Pdual,I)`.

Here alpha and beta are actual postcomposition, and gamma is actual
precomposition by alpha. K-projectivity of P and Pdual makes alpha and
beta quasi-isomorphisms; K-injectivity of I does the same for gamma.
`evaluation_coefficient_naturality` proves the literal signed equation

`evaluation(P,I) ≫ gamma = evaluation(P,S) ≫ beta`.

Two-out-of-three proves quasi-isomorphism of that same evaluation.
Its original source naturality then transfers the result along q.
The passed double-coinduction evaluation square and native reflection
of quasi-isomorphisms by scalar restriction give the result for the
already A-linear evaluation. `derivedEvaluation_app_Q` supplies the
original localization formula. Naturality handles the displayed
representative isomorphism to T.

For a chosen ordinary injective resolution of W, existing
`Adjunction.isKInjective_map_of_injectiveComplex` proves K-injectivity of
J from the actual bounded-below injective terms and preservation of
monomorphisms by restriction. No bounded injective-dimension theorem is
needed. The abstract result does not require sigma to be finite or flat.
For arbitrary sigma, J represents the coinduced derived coefficient;
identifying it with `Hom_R(A,R)[0]` additionally uses projectivity of the
original restricted A-module and exactness of coinduction. In the
regular-base surface application those are supplied by the passed
finite-normal-algebra and projective-coinduction results, assuming the
actual F2 ring map.

The current surface consumers are C, its dual and the residue object in
degree one. Their concrete finite-projective models remain separate:
the model for C must use the actual Postnikov connecting morphism and
retain the possibly nonsplit H1 extension. The actual finite-length
resolution and universe transport, residue-line and input-shift
comparisons, surface concentration, original trace, V2 and GR are not
conclusions of this file.

Source basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. Native
compilation is coordinated by the principal; the author retains coupled
proof repair. The classical bounded finite-projective argument is also
described in [Stacks, Lemma 07VI](https://stacks.math.columbia.edu/tag/07VI)
and [Stacks, Lemma 15.75.2](https://stacks.math.columbia.edu/tag/0A5W).
