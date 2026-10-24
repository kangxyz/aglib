> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#transport-section-equivalences-before-specializing-the-qc-pseudofunctor) · [Context](original-context.md) · [Case index](README.md) · [Previous record](picard-pullback-parameterize-the-target-unit-before-specializing.md) · [Next record](original-represented-étale-cohomology-normalize-complete-values-before-specialization.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Transport section equivalences before specializing the QC pseudofunctor

At the same Lean/Mathlib pins, constructing `NatIso.ofComponents` directly on
the concrete QC pseudofunctor Hom/section equivalence in
[SectionsNaturality](../../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/SectionsNaturality.lean)
exhausted the standard 200000-heartbeat budget at `whnf`.
The existing observation is `qc-coefficients-02.log`, line 38:67, after 17 seconds.

Define `transportTypeFunctor` and `transportTypeFunctorIso` for an arbitrary
Type-valued functor and objectwise equivalences. Instantiate that abstract
natural isomorphism once at the native `homPresheaf` and `sectionsEquiv`.
This retains the original presheaf, actual sections of the pulled-back module,
restriction maps, and fpqc/fppf sheaf interfaces.

The exact repaired leaf, SHA256
`fdb58c9f5aac9efb149e2fee9b3ea21f8416fa0f15ceab627dcd992ad43b7dca`,
passed in 2.9 seconds in `qc-coefficients-04.log` without a budget increase.
This is an existing successful compile observation, not a controlled benchmark.
The separate SectionUnit, SectionsRestriction, EtaleSections and AmitsurProducts
consumer failures in that invocation are excluded from the success claim.

The same principle also applies to
[SectionsRestriction](../../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/SectionsRestriction.lean).
Its concrete `mapComp` rewrite exhausted 200000 heartbeats at `whnf`
(`qc-coefficients-06.log`, line 48; 99 seconds). The abstract
`nativePullHom_eq` helper first pastes the existing component equalities with
`congrArg₂`, then specializes to the QC objects. The repaired leaf, SHA256
`a69299432bc13eb992c6d7a5692ceedab0575bb49a7b8a6e10e71b3d4c76ec2d`,
passed in 118 seconds in `qc-coefficients-07.log` at the unchanged budget.
This eliminated that heartbeat failure; it is not a wall-time speedup claim.
Original pullback/pushforward units and `pullbackComp`/`pullbackCongr` maps are
retained. The separate additive-coefficient consumer was still under repair.

### Stage subtype equalities before concrete matrix equivalences

In the actual crossed-product
[coefficient equivalence](../../Aglib/FieldTheory/Brauer/CrossedProduct/Coefficients.lean),
a one-term `Subtype.ext (fromCoefficients_row hc h₁ x.property)` exhausted
200000 heartbeats at `whnf` (`brauer-cocycles-01.log`, line 94:29).
The repair explicitly types the full-indexed matrix in `toFun`, applies
`Subtype.ext` first, changes the goal to the original matrix equality, and
then applies `fromCoefficients_row` with the original membership proof.
The right-inverse proof similarly uses `funext`, an explicit `change`, and
the actual row identity instead of asking elaboration to discover all carrier
conversions inside one term.

The complete repaired producer, SHA256
`b67ae05a1e98a43e65686bd3748e4a3198add570329386462e26567e5e19b81f`,
passed in 3.7 seconds in `brauer-cocycles-03.log` at the unchanged native
200000-heartbeat budget. The intermediate graph 02 removed the first timeout
but still had a right-inverse error; only graph 03 establishes acceptance.
This validates the typed-staging repair, not a controlled timing comparison
or acceptance of the downstream centrality/simplicity/primitive producers.

### Transport complete additive naturality before specializing geometric sections

The additive transport boundary must include naturality, not only the component constructors.
In `qc-coefficients-26.log`, the final
[unit structure comparison](../../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/StructureComparison.lean)
`NatIso` still exhausted 200000 heartbeats at `whnf` after individual lifted
additive components had been abstracted. The repaired `liftTransportNativeIso`
in `AdditiveTransport` proves the entire naturality square over arbitrary
`P`, `A`, `e`, `r` and the native additive target `Q`, before specializing to
scheme sections. The concrete `unitSectionsAddEquiv` and its actual native
unit-section naturality theorem remain unchanged.

The full StructureComparison producer, SHA256
`7760ceaf3f01c3048fb4ea2b08c9a2b12e3ac4985ba087de06dde1832534dce3`,
passed in 12 seconds in `qc-coefficients-28.log`; AdditiveTransport, SHA256
`ac88e351a741f7986b78b76ccbe28fa40262693994ad9384c087731cd0d85722`,
passed in 4.6 seconds, with the unchanged native budget. These are acceptance
observations, not a controlled speedup or acceptance of CoefficientMaps,
BaseRestrictionAdditive, or the downstream cohomology comparison.

For base restriction the analogous full-boundary repair is
`liftTransportIsoOfTypeIso`: prove the Type-natural-isomorphism-to-additive
transport abstractly, then supply `sectionsBaseRestrictionIso` and the named
component evaluation equality. This retains the original `pullbackComp`
components. The concrete section-naturality specialization in
`qc-coefficients-30.log` exhausted 200000 heartbeats at `whnf` (49-second leaf).
BaseRestrictionAdditive, SHA256
`9a70f8e1fd1be4bc88aa422d1ad4a94f6954f9b9b356f33ca4d8eb1452f3a6ba`,
passed in 38 seconds in `qc-coefficients-32.log`; the expanded AdditiveTransport,
SHA256 `c53d9228e314117d956f3f81453399d8683594bd596a3fe589ad3855bfe6f6a6`,
passed in 5 seconds. Budgets were unchanged. This validates that boundary,
not a controlled timing comparison or the pending coefficient-map/Amitsur consumers.

For maps on the same site, also absorb the identity functor and left unitor
inside the abstract transport helper. The concrete `liftTransportHom`
specialization in `CoefficientMaps` still exhausted 200000 heartbeats at `whnf`
in `qc-coefficients-31.log`. `liftTransportHomSame` checks that complete
same-site construction before geometric specialization, retaining the actual
`coefficientSectionsAddHom` and original coefficient naturality. After ordinary
identity/composition normalization in graph 32, CoefficientMaps, SHA256
`b4e0e2250ce17e33e507c15900aee7ba6661c109f339facf0c3010191cbc416a`,
passed in 12 seconds in `qc-coefficients-33.log`, with no budget increase or
separate benchmark.

The original Amitsur-to-Cech transport needs the same full boundary for
opposition and whiskering. In `qc-coefficients-39.log`, the concrete
opposite-diagram isomorphism/section-whiskering conversion exhausted 200000
heartbeats at `whnf` (21-second failed leaf). Generic `rightOpSectionsIso`
checks the inverse identities and functor-composition conversion before any
scheme/module specialization. The original geometric isomorphism, coefficient
and `amitsurCechSectionsIso` interface are retained. AmitsurCech, SHA256
`6f10c40dc35b0d57761531f980fc4b26fd6389c752c7a4245bc528fbcc3a4d5a`,
passed in 3.3 seconds in `qc-coefficients-40.log` with the same budget; this is
acceptance evidence, not a controlled speedup or a Zariski-consumer acceptance.

For the final original Zariski module-coefficient naturality square,
`qc-zariski-06.log` hit maximum recursion depth in one `change` computing
sheaf-preimage, open inclusion, transport and `ULift.down` simultaneously
(7-second failed leaf). The repair first proves `zariskiModuleIso_hom_app`
at the bundled-morphism level, retaining the opaque original presheaf iso
and using only the actual identity/map-identity equations. Consumers rewrite
that named equality before evaluating `down` by `rfl`. The original component
formula and coefficient naturality are unchanged. ZariskiModuleCoefficients,
SHA256 `adf2847e95382b4fee2adf79dd7e89023b664ba43b0729c85517aa67a0aef6e5`,
passed in 16 seconds in `qc-modules-01.log`. No recursion/heartbeat limit was
raised, no benchmark added, and downstream original-H wrappers were not part
of that acceptance.

### Fix site objects before applying a generic finite-sum descent theorem

The finite-etale trace gluing producer exhausted 200000 heartbeats in
`isDefEq` at `chartSum_independent` in `finite-trace-08.log`: the target of the
chart morphism was still unresolved during specialization. Supplying the
actual `(X := X)`, `(V := V)` and `(U := (toEtale X).obj Y)` to the existing
generic independence theorem removed that timeout in graph 09. Graph 09 still
had unrelated projection/linter diagnostics; only `finite-trace-10.log`
accepted the complete Gluing producer (6.1 seconds), SHA256
`ff0fe364e1fe5f53cf507d3f48f560e110bb2cf7afe18308bd34e78c3688c915`.
No budget increase or separate timing experiment was used. The original sums,
local transition maps and finite-flat rank equation remain unchanged; this
receipt does not certify the downstream normalized trace/source square.

### Specialize a complete coproduct projection identity, not its intermediate rewrites

The actual generic-Artin pullback point-index producer repeatedly failed to
normalize the projection through `pullback (Sigma.desc ...)` versus
`pullback (genericArtinMap X)`. In `generic-discrete-09.log`, even the requested
`Category.assoc` rewrite did not match across that wrapper. This was an
elaboration/normalization failure, not evidence of a resource timeout.
Prove the entire first-projection identity for an arbitrary literal family of
schemes and maps; only then specialize the completed identity to the original
generic-Artin map with `exact`. The native Sigma inclusions, pullback symmetry,
finite-coproduct comparison and literal projection equation are unchanged.
GenericArtinBaseChangeIndex, SHA256
`89edc71d5f135c1679a4e90c712f3a507066dd5985d911c4b53acc430d3309be`,
passed in 4.9 seconds in `generic-discrete-10.log`. No budget increase or
separate benchmark was used; the receipt does not validate later support
consumers.

### Pin the existing Ext universe before specializing a concrete fibre

In `root-b3-03.log`, the final characteristic-primary restriction wrapper hit
the 20000 typeclass-synthesis heartbeat limit trying to reconstruct `HasExt`
through the local `Over.left C` abbreviation. The original target fibre already
had the required `HasExt` instance. Install that exact instance on `C.left` with
`inferInstanceAs`, then apply the accepted vanishing theorem with its explicit
Ext universe. Also rewrite the chosen degree equality rather than letting
`subst` pick a differently oriented arithmetic equality. No new cohomology
model, universe equality assumption or budget increase is needed.
CharacteristicPrimaryRestriction, SHA256
`69df63d03c2623e63892604a19155528a2046f355442e94e061bd64cb3988fae`,
passed in 35 seconds in `root-b3-04.log`. This acceptance is the actual
characteristic-primary original restriction endpoint, not the remaining
prime-to-characteristic curve branch.

### Type the original Hom endpoints before expanding an adjunction composite

`finite-trace-14.log` exhausted the standard 200000 heartbeats in `whnf` while
evaluating the composed adjunction for the finite-etale source comparison
through concrete small-etale wrappers. Fix the full Hom type first, from the
actual slice integer coefficient to `inverse.obj A`; compose typed
`congrArg`/`trans` identities rather than rewriting beneath unresolved
adjunction wrappers. Select the original slice exactness instance explicitly,
`overPullback_preservesFiniteColimits.{u+1,u,u+1}`, where universes are otherwise
underconstrained. The source and target Ext universes remain independent.
SlicePullback.SourceSquare, SHA256
`3e2b3330ec34033a7f5beec764a756150a55104949d20c93349c5c2595b5637d`,
passed in 69 seconds in `finite-trace-16.log` without raising any budget.
This validates the literal original pullback/source square, not the later
finite-field scalar-transfer injectivity consumer.

The same explicit-Ext pattern applies to original field pullback effacement.
In `field-dimension-04.log`, `PullbackEffacement` reached the native 20000
instance-search limit while reconstructing `HasExt` through
`(Functor.fromPUnit X).obj U.right` and the finite-field-cover chart wrapper.
Fix `(X := X)` and `(S := U.left)`, then transport the existing chart `HasExt`
with `inferInstanceAs`; do not ask typeclass search to rediscover it beneath
the geometric wrapper. The next graph's ordinary `map_zero` rewrite failure
was separate: under implicit transparency, the unfolded `@Etale` property did
not match its bundled `MorphismProperty`. Typed additive-equivalence aliases
and complete `congrArg`/`Eq.trans`/`map_zero` identities avoid rewriting there.
PullbackEffacement, SHA256
`45f19c79c2a7a9d194e968b34df0410ab12c85c7ea323866d0ae4bf62b79fb5e`,
passed in 37 seconds in `field-dimension-06.log`; its original dimension-shift
consumer passed in 26 seconds. These are acceptance receipts, not a controlled
speedup measurement. Original maps, independent Ext universes and all budgets
are unchanged; the geometric finite-coinduction and H2 inputs are separate
suppliers, not certified by this consumer graph.

### Stage pointed fibre identities before specializing field restriction

In the field-restriction graph, specializing the entire pointed precomposition
identity at the native field chart made elaboration and kernel checking unfold
large concrete fibre and Galois constructions. `field-sylow-10.log` recorded a
kernel deterministic timeout (97 seconds); `field-sylow-11.log` and
`field-sylow-12.log` reached the unchanged 200000 weak-head-normalization budget
(35 and 21 seconds). These are distinct failure receipts, not benchmarks.

Prove the fibre-component identity first with an abstract typed scheme map,
pointed fibre and cover. Derive the pointed-map identity from that statement,
then specialize to the native field map in a separate opaque theorem. The
accepted staging uses `pointEnd_left_restrictScalars`,
`pointedFiber_toFibreAut`, `pointedMap_toFibreAut_of_map`, and finally the
canonical field/Galois comparison. Explicit source, target and scheme
parameters keep instance reconstruction out of the concrete final application.
`Field.Restriction`, SHA256
`322ddfbd7a75809a1a603807f9b838c0057789c88665c6ef4f14c825fff13e71`,
passed in 4.3 seconds in `field-sylow-13.log`, without increasing any budget.
This certifies the original restriction comparison only; the subsequent Sylow
and finite-coefficient H2 theorems require their own acceptance receipts.

A separate kernel-memory failure occurred in `SylowMonodromy` at line35:8
in `field-sylow-17.log` (83 seconds): elaboration had completed, but the concrete
native fibre-equivalence power transport exceeded the unchanged memory limit.
Extract the entire conjugation through `autEmbedding` and the fibre equivalence
into `FundamentalGroup.PointedPower.component_pow_eq_one_of_pointedMap`, with
the actual pointed map, automorphism, cover and exponent abstract. The concrete
field theorem then uses the component identity and one opaque application.
The proof still uses the original pointed maps and field restriction data.
In `field-sylow-18.log`, PointedPower (SHA256
`e880022d25300827ed32462e7314458b22ad0ec4969fac6e2032349580fa5c90`)
and SylowMonodromy (SHA256
`a5d9c9668b032868713461900c696820d9134da2ee474aeb4c93bbaa1f559556`)
passed in 2.9 and4.6 seconds. The graph then failed in the downstream SylowLine
consumer. These local receipts do not certify that consumer or the finite-H2
endpoint, and no resource ceilings were increased.

### Use native sized subobject infima instead of rebuilding a concrete lattice

For the actual point-supported subobject of an original abelian etale sheaf,
complete-lattice inference reached the unchanged 20000 typeclass budget in
`generic-support-06.log` (130 seconds). A later explicit lattice still made the
concrete infimum bound normalize too much: `generic-support-11.log` reached
200000 weak-head-normalization steps (47 seconds).

Keep the native Grothendieck sheaf structure and express the same infimum as
explicitly sized `Subobject.sInf` of the range of the original kernel family.
Use native `sInf_le`/`le_sInf`, an abstract kernel-factorization relation, and
native downward AB5 for the actual point fibre. This avoids reconstructing an
unused concrete complete lattice; it does not assert that a fibre preserves
infinite infima. PointSupportedSubobject (SHA256
`0aee711895e260d4290840b065e3ddb3569e48a3a0f1c6da71ffe1e1a4518a15`)
passed in 4.3 seconds in `generic-support-13.log`, and the closed-unit consumer
passed in 2.6 seconds. Exhaustion and higher-cohomology consumers are separate
unaccepted targets at this checkpoint. No budgets were raised; these are
acceptance receipts rather than a controlled performance comparison.

The same explicit-Ext transport also resolved the actual generic higher-image
consumer. In `generic-higher-03.log`, GenericHigherImages at112:13 reached the
unchanged 20000 typeclass budget while reconstructing localized Hom smallness
on the literal pullback behind a chart wrapper (102 seconds). Install the
`HasExt.{u+2}` for that pullback with `inferInstanceAs` from the existing
`HasExt.{u+2}` on the chart's `T.left`, and specify the power theorem's
`.{u,u+2}` universes. GenericHigherImages (SHA256
`71feb1d19cd0d7b6b93fabc2bf024f80dbdc9883af98ee72650c66b74668baf4`)
passed in 66 seconds in `generic-higher-04.log`; its original direct-image
cohomology divisibility consumer passed in 7 seconds. These validate the
unchanged actual sheaves and maps, not a controlled speedup comparison.

