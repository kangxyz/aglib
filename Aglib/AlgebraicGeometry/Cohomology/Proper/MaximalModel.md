# A maximal original first-cohomology model

[MaximalModel.lean](MaximalModel.lean) constructs an actual normal proper
birational model attaining the largest original H1 length allowed by a
uniform bound. It then proves bijectivity of every original structural H1
map to a further normal proper birational model.

The endpoint is `AlgebraicGeometry.Scheme.Cohomology.exists_maximal_normalModification`.
Its inputs are a commutative domain A, `IsIntegrallyClosed A`, and the genuine
previous theorem input `NormalModificationH1Bounded A`. No locality,
Noetherianity, dimension, resolution, chosen maximal model, or assumed
cohomology isomorphism is an input to this step.

The output is a natural number n and an integral normal scheme X with an
actual proper dominant f:X→Spec A whose original function-field map is an
isomorphism. The original structural A-length of H1(X,O_X) equals n, and
the same length on every normal integral proper birational A-model is at
most n. For every actual proper dominant g:Y→X, with Y normal and integral
and with its original function-field map an isomorphism, the output proves
bijectivity of exactly

```lean
moduleCohomologyMapAlongLinear g (FiniteTraceCoordinates.structureScalar f)
  (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1
```

The structure module is always the original
`FiniteTraceCoordinates.structureModule`. On Y the displayed map uses the
original action `g.appTop.hom.comp (FiniteTraceCoordinates.structureScalar f)`.
The equality with `FiniteTraceCoordinates.structureScalar (g ≫ f)` is proved
directly from composition of the original section maps. No action is
transported along an arbitrary additive equivalence.

`originalStructureH1Length` records the original length with these explicit
actions. The identity of Spec A makes the family nonempty: its actual stalks
are normal localizations of A. Its original identity function-field map is
an isomorphism by the composition equation and injectivity, with each
original element as its own surjectivity witness. No chosen field
isomorphism is introduced.

Every bounded extended-natural length is finite before `ENat.toNat` is
used. `Nat.findGreatest` on the predicate of attained natural lengths gives
an actual maximum, including the zero case. This does not require a
parameter space for models. The lower
`exists_maximal_normalModification_of_model` isolates this argument for
any genuine seed model and is consumed by the final normal-ring endpoint.

`original_structureH1_bijective_of_maximal` applies the proper
birational original-map injection to g. The actual composite g≫f is another
member of the bounded family, so the source and target lengths are equal
and finite. The original injective map identifies its source with its range.
The native strict length inequality for a proper submodule rules out a
proper range and proves surjectivity of that same map.

This result does not assert R1 g_*O_Y=0. That continuation needs the original
low-degree Leray comparison, the requisite H2 vanishing or injectivity, and
a justified passage from global sections to the actual higher direct-image
sheaf. Treating arbitrary local modifications also requires an actual
spreading or domination construction and the original localization
comparisons. No rational-model, local-resolution, or full-resolution
conclusion is included here.
