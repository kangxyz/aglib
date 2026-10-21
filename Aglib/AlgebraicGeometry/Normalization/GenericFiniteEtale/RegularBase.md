# Regular-base normalization: consumer correspondence

`RegularBase.lean` supplies
`AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.etale_of_regularStalks`.
For integral, locally Noetherian `X` with regular actual stalks and every
`C : Scheme.FiniteEtale (Spec X.functionField)`, it proves that the actual
relative-normalization structure morphism is etale from the actual target
codimension-one stalk-base-change condition. The generic cover may be disconnected
or empty. The statement has no characteristic or dimension bound and retains
the consumer's scheme universe `u`.

## Fixed consumer and map correspondence

The consumer is `normalization_etale`, lines 126–161 of the supplied packet file
`sources/lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/Etale/NormalizationCriteria.lean`,
SHA-256 `5fcdd6f2046dd320493968db06a07ac2407429ce303101742063d2119b465a85`.
This is a new application of purity, not a claim to implement its former
all-quasi-finite `Stacks0BMB` interface.

The original `Normalization/GenericNormalization.lean`, SHA-256
`6afe585ba6049b6e5a1b2f9b5ca5913f8b7af9f9d3e99366fc776397fe0a76b3`, defines:

- `originalMap X C := C.obj.hom ≫ genericInclusion X` at line 43;
- `normalization X C := (originalMap X C).normalization` at line 49;
- `structureMap X C := (originalMap X C).fromNormalization` at line 52.

The original `Normalization/GenericFullFaithfulness.lean`, SHA-256
`7246e5f4be0af6b659735963b32dff165ac2be42aee13578fc4efb4dfa1e8fc0`, defines
`genericInclusion X := X.fromSpecStalk (genericPoint X)` at lines 55–56.
The original `Stalk/CodimensionOne.lean`, SHA-256
`7c4d89b447ffdf90267c8be33bdfcd7bcf22098ca6ff491049bee51dd4a56888`, defines
`CodimensionOnePoint X := {x : X // ringKrullDim (X.presheaf.stalk x) = 1}`
at lines 57–58. Its native owner retains exactly that subtype.
Thus unfolding the source wrappers gives the new theorem's literal objects,
structural morphism, target points and pullback projections; no replacement
normalization or supplied identification is involved.

## Removed premises and proof

All three old theorem-family parameters are removed:

1. `Stacks0BMB` is replaced, for this finite generic-normalization consumer,
   by `Algebra.etale_of_unramified_height_one_of_isRegularRing` on each affine
   integral-closure field factor.
2. `NormalizationLocalDimension` is supplied by the native
   `GenericNormalization.stalk_ringKrullDim`. Consequently a source stalk of
   dimension one maps to precisely the target point indexed by `hlocal`.
3. `EtaleFromStalkBaseChange` is unnecessary: the native
   `Scheme.LocalRing.Etale.stalkMap_formallyEtale_of_etale_stalkBaseChange`
   transports the literal pullback's etaleness to the original stalk map.
   Only its formal-unramified part is needed.

The separate base-stalk `IsIntegrallyClosed` hypothesis is also removed, since
`IsRegularLocalRing.isIntegrallyClosed_of_regularLocal` derives it. Finiteness
of the normalization, local Noetherianity, and the affine normality and
dimension comparisons use existing native providers.

For a nonempty affine target open `U`, let `R = Γ(X,U)` and let `A` be the
sections of the given `C` on the literal preimage of `U`. The native chart
instances make `A` etale over the actual `K = X.functionField`; their scalar
tower uses the actual generic germ and structural map. The decomposition
`A ≃ₐ[K] Π i, L i` has finite separable field factors. The actual integral
closure is identified by `integralClosure.equivPi` with
`Π i, integralClosure R (L i)`. This includes the empty product.

Each factor is a finite normal domain over the regular domain `R`, with fraction
field `L i`. Its `FractionRing R` action is explicitly transported through
`FractionRing.algEquiv R K`; separability is transported along the same map.
The factor spectrum maps by an open immersion into the original integral-closure
chart. Its height-one prime has the same stalk dimension in that chart and in
the actual global normalization. The existing dimension theorem sends it to
the original target divisor. `hlocal`, stalk-map composition, and the canonical
`Scheme.arrowStalkMapSpecIso` then give unramifiedness of the original factor
algebra at that prime. Purity applies with these literal maps and scalar towers.
Finite-product etaleness recovers the original integral closure. The original
`fromNormalization_app` identifies the chart map, and target locality glues.
Empty target charts are handled directly by their empty-scheme instance.
The proof never asserts that the total normalization or generic cover is a domain.

## Dependency and execution boundary

The new algebraic-purity provider is
`Aglib/RingTheory/Etale/ZariskiNagataPurity.lean`, SHA-256
`4271c791df0b5fd1f6bb351f1ca050dc38c65c313b8c777903ee668ace05eea2`.
Those bytes match the supplied `purity-20261021T004536Z/aglib` snapshot and the
release checkout at `558fad66ff831d9c277e0e08c43e23783c175e6e` with the assigned
uncommitted provider batch. The principal owns its pending combined execution
and mathematical adoption. This sidecar makes neither an established-status
claim nor a claim that full pointwise quasi-finite branch purity follows.

The adapter body compiled successfully against the warm release cache with an
explicit temporary copy of precisely the provider's algebraic-purity interface.
That authoring fixture is preserved as
`/private/tmp/r5-investigations/aglib-full-20261021/purity_normalization_adapter/RegularBase.assuming-purity.lean`,
SHA-256 `6675c1aaa97d947575f04572f23fe92fa5efc095db3c71ce904195fe1389480a`.
Its exact changed-target build exited zero; log and native receipt are
`build-005.log` and `build-005/graph-build.json` in that scratch directory.
The cache probe required only `RegularBase`, and the build performed no cold
foundation work. That result establishes the adapter with the displayed
temporary input, not the final theorem's compiled closure.

The delivered source removes the fixture, imports the actual provider and calls
its proved theorem. Compilation of those final bytes and the three clients in
`AglibTest.RegularNormalizationPurity` is pending the principal's combined
authorized graph. Those clients cover the generic interface, the actual empty
cover and a concrete split algebra `Fin 2 → K`. No independent lint, test run,
audit or kernel replay is claimed by this handback.

The exact target command, in a workspace with the matching purity dependency
cache, is:

```sh
python3 scripts/build_serial.py --receipt-dir /absolute/fresh/receipt-directory \
  Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RegularBase \
  AglibTest.RegularNormalizationPurity
```

Only these new Lean, sidecar and client files are owned by this assignment.
Existing providers, packet consumer, facades, README files and Git state are
read-only; the principal owns their integration.
