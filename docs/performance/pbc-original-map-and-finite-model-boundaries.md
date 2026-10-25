# Private PBC compilation boundaries

These complete records retain the current mainline's already written conditions,
repairs, source identities and ordinary incremental evidence. They concern
private proof candidates; they do not assign publication or PBC status.
The applicable toolchain and workflow are in the [performance guide](../PERFORMANCE.md).

## Isolate concrete cohomology-colimit relation extraction

In the private PBC mainline on 2026-10-24,
[StageCohomology](../../Aglib/AlgebraicGeometry/EtaleCohomology/Fields/SeparableExtension/FiniteConstants/StageCohomology.lean)
exhausted 200000 heartbeats at `whnf` in the direct application of
`Concrete.isColimit_exists_of_rep_eq`. Naming the actual group diagram and
cocone inside the scheme-limit proof had not removed that failure.

The repaired source extracts that application into a private lemma over an
abstract `D : J ⥤ AddCommGrpCat`, with explicitly fixed morphism type
`FC := fun A B => A →+ B`, carrier `CC := fun A => (A : Type _)`, cocone and
indices. The scheme theorem applies it to its same original cohomology
diagram. All original relation equations and hypotheses are retained.

Failed source `eb6691821763b41f7659c5567775a77adaca7f7c7b063f4f5c8907cd6068df26`
failed after 74 seconds in `remote-6b87fba54d9a49b2832cf6035a5ac0af`.
Source `1871b10dcd94c481f41dbab11ea9417f4e7eb7c1854c240e8e59e521cb27df0d`
passed after 79 seconds in closed run
`remote-2d2d5f7a463e47af84371a0ebfb63478`, with compiler exit zero and unchanged
default budgets. Other modules failed in that batch. This establishes removal
of the recorded budget failure; it does not show a wall-time speedup or closure
of the field-comparison graph. The exact failed and passing inputs, receipt
and compiler events are retained in the mainline task's evidence handback.

## Extract original zero witnesses before concrete constant normalization

The private
[FiniteTypeCohomology](../../Aglib/AlgebraicGeometry/EtaleCohomology/Fields/SeparableExtension/FiniteConstants/FiniteTypeCohomology.lean)
zero-descent theorem exhausted the ordinary kernel budget in
`remote-a04981fb339346cea0e9382c8ac640b3` after 549 seconds. Its concrete proof
combined original scheme-limit cohomology, zero-witness extraction and the
constant-coefficient comparison in one construction.

The repair reuses the site-level original-map producer
`Stalk.exists_pullback_eq_zero_of_colimit` from
[ChartLimitZero](../../Aglib/AlgebraicGeometry/EtaleCohomology/Stalk/ChartLimitZero.lean).
It receives the actual coefficient diagram, cone, cocone, colimit proof and
original zero class. The concrete caller supplies the exact quantified Ext
dictionaries for both constant diagrams. The returned raw zero equation is
transported through the same original constant-sheaf comparison by typed
`congrArg`, followed by its map-zero law. Rewriting inside the semireducible
constant-diagram carrier had failed despite identically printed expressions.

`ChartLimitZero` source `93b54b3c...` passed in the closed run
`remote-37f1a66861cf48e3a2162d4ebde21b10`. The complete repaired finite-type
source `704a901e96f6c38cce5b300d20cf7b90f0e51788ea9e38e8708e9401c2a66aee`
passed in `remote-a19efd65fff64382916752bb7bca915a` in 324 seconds; its next
`FieldComparison` consumer also passed in that batch. These are ordinary
producer results on Lean 4.34.1 and the pinned Mathlib, with unchanged
200000-heartbeat and resource limits. Other consumers in the batch failed.
No controlled speedup, unique explanation of kernel cost or completed PBC
endpoint is inferred. The source packets, log and compiler events remain
with the private mainline evidence.

## Evaluate the original finite exchange after forming its whole isomorphism

The private `NoetherianModels/EmbeddingTransport` consumer encountered a
kernel timeout while proving invertibility of the finite ordinary exchange
after specializing to a concrete constant sheaf. The original failed graph
also contained ordinary source-name and implicit-argument errors; the
observations do not isolate a unique source of kernel cost.

The accepted construction first obtains `finiteBaseChange_isIso` for the
whole original natural transformation, packages it as a natural isomorphism,
and only then evaluates at the original constant coefficient. It composes
that component with the same native constant-sheaf pullback isomorphism and
the original finite-product comparison. The finite embedding record keeps
its actual index, schemes, finite maps, value groups and monomorphism.
No general proper-base-change premise or replacement exchange is introduced.

The complete `EmbeddingTransport` frontend passed in 6.8 seconds in
`remote-0ef5718e254740a2a6626a8b119dd58c`, on Lean 4.34.1 and pinned Mathlib,
at the ordinary resource limits. The source and compiler correspondence are
recorded in `universal/notes/pbc-retained-0ef5718e.json` in the mainline task
workspace. Its downstream Noetherian-model consumers remain separate
frontiers. No extra benchmark or replay was run.

## Factor cohomology composition before specializing native scheme isomorphisms

The private
[NativeLineComparison](../../Aglib/AlgebraicGeometry/EtaleCohomology/Fields/SeparableExtension/FiniteConstants/NativeLineComparison.lean)
adapter repeatedly exhausted the ordinary 200000-heartbeat `whnf` budget
when transporting the categorical projective-line field comparison to the
original native line map. Abstract bijectivity cancellation alone, and typed
aliases for the concrete projection and isomorphism, left the original
cohomology composition and inverse-image coefficient transport specialized
to those schemes during conversion.

The accepted repair puts the complete composition argument in a private
lemma over variable schemes, an actual scheme isomorphism and its original
factorization equation. It applies `cohomologyPullback_comp`, keeps the
actual `inverseImageComp` coefficient isomorphism, and cancels its original
cohomology map. Only the finished bijectivity statement is specialized to
`lineOverBaseChangeIso`. The public theorem retains the literal
`lineBaseChangeMap`, the same killed-by-n hypothesis and independent original
Ext universes; no proper-base-change premise is introduced.

Exact repaired source
`978dfb257512d49a702a190396d5a24c5994955dbb5f23f283376374031695f9`
passed in 42 seconds in closed run
`remote-d03e0d6af92a4560ae9b951c85bdea4c`, source snapshot
`bf306af19aa1472cece5547743b1286b4549bdfa3d7394fdecab52c4997d30a6`,
on Lean 4.34.1 and the pinned Mathlib with unchanged resource limits and
options. Two independent model/presentation frontends failed in that run.
This records the adapter's ordinary compiler closure, not a controlled
speedup or completion of general PBC. No additional benchmark or replay was run.

## Abstract the complete original stage-Hom transport

The private `NoetherianModels/FixedTargetHom` consumer combined original
right-tail Hom continuity with dependent inverse-image triangle transport,
colimit-unit comparison and adjunction cancellation. The first concrete
version failed ordinary native-alias rewrites and reached both `isDefEq`
and kernel `whnf` budgets in `remote-374dcea69e4146d185181ff3e46d5226`.
The failures included `Functor.map_id` not matching an actual functor alias
and a cocone point still expressed through a constant diagram.

The accepted version performs three entire calculations before scheme
specialization: dependent transport of a mapped equality into the actual
triangle, target-isomorphism factorization of a lifted Hom, and the
unit/cocone/adjunction eventual-equality chase over a family of categories.
Its concrete caller gives explicit original source and target schemes,
the actual right-tail cocone, native stage isomorphisms, and the already
proved original Hom-continuity producer. The same model maps, `hr`, `hc`,
canonical-stage hypothesis and original limit equation are retained.

Exact source
`56ba2be06f0c6668ba21d0b1498f4ee0a382c6ef4cb9d07bdfd62ac06af114c0`
passed in 107 seconds in `remote-3d2540d644b2420eb8bb081dd1ddb874`, source
snapshot `3deda0cd1cfe041e3187383d69bfc2044736c10be90cb8436e8c74984009d080`.
The unchanged Triangle and Data suppliers had passed in the preceding run.
The upper `HomAbove` consumer failed because its theorem did not include
the used `hc` section variable; full model descent is not inferred here.
The pinned toolchain, options and resource budgets were unchanged. These
are ordinary compiler results, not a controlled speedup; no extra replay
or profiling was run.

## Normalize native chart cycle producers before representative pairing

The private `Stalk/BaseChangeChartSections` consumer reached the ordinary
200000-heartbeat kernel `whnf` budget while combining native chart maps,
resolution witnesses and the generic representative exchange. Abstracting
the chosen injective resolutions and higher arrow alone did not close
that boundary: source `0044b924...` still failed in
`remote-976e61426a7e4c17962e3de996f47af2`.

The accepted construction separately proves four native-typed identities:
the original ordinary section square, original lift evaluation, source
cycle conversion to section-functor maps, and target cycle conversion to
the literal fibre-product chart. The generic representative argument then
consumes those theorem constants. Surplus Ext and derived-model parameters
were omitted from the private helpers where they were unused. The public
theorem retains the original higher exchange, presheaf edge, chart class,
all-degree quantification and independent Ext/derived models. No global
extension of a represented class or arbitrary injective-preservation
premise was added.

Exact final source
`568e85ad440156d686eabd48b69ae158978c5b09ea5db7e1b01245fcdd8e01f2`
passed in 294 seconds in `remote-7d3a66f1525447858279716f091f8a36`, source
snapshot `5687925befc2ad09b7c832df26306c7bd024266cb3892d882f6066afd3186ba0`.
The pinned compiler, options and budgets were unchanged. This is ordinary
compiler closure of CH; the neighborhood exchange and common-point diagram
remain separate consumers. No controlled speedup or extra replay is claimed.

## Normalize complete pointed-cohomology maps before evaluation

The private [ChartGeometricComparison](../../Aglib/AlgebraicGeometry/EtaleCohomology/Stalk/ChartGeometricComparison.lean)
consumer reached a kernel deterministic timeout in its original pointed-germ
formula. Source `3f5eb0c1...` failed after 247 seconds in
`remote-7d3a66f1525447858279716f091f8a36`. Abstract composition alone had left
the concrete pointed leg and strict-local comparison to normalize at the
final scalar class.

The repair retains three complete additive-map identities: the original
strict-local comparison on each original pointed germ, the original pointed
leg followed by geometric restriction, and their composition as the actual
public comparison. The last scalar theorem only evaluates the completed map
identity. Typed projection equations retain the original geometric point
and the original cone leg; no comparison between marked models is chosen.

Source `ef433fdcec3bc10a38c1390cdf0025dc98fb9c0c85cda2c2714f9202c46d55ca`
passed in 301 seconds in `remote-ebb893e191d84a54bd048f577ff67234`, on the
pinned toolchain and unchanged budgets. This establishes ordinary compiler
closure of the germ formula, not a speedup. Bijectivity still requires the
actual local-to-geometric cohomology transfer; neither that input nor PBC
follows from this formula. No extra benchmark or replay was run.

## Transport finite diagram arrows before specializing coefficient categories

The private [FiniteDiagrams](../../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/PositivePresentation/NoetherianModels/FiniteDiagrams.lean)
induction combined stage-Hom lifting, inverse-image transport and insertion
into a dependent finite family. The repair isolates transported old and
new arrow equations over abstract functors and isomorphisms, and isolates
typed dependent-family insertion before the concrete coefficient induction.
Finite diagram equations remain actual eventual equalities, not additional
model hypotheses. On this pin, the final dependent branches use
`dite_eq_left` and `dite_eq_right`; the older names are deprecated.

Source `a9eba1d9...` passed in 9.2 seconds in
`remote-ebb893e191d84a54bd048f577ff67234`. Its subsequent `HasStageModel`
return annotation was changed from the identical raw predicate to the native
`ObjectProperty`, allowing downstream field notation to resolve correctly.
That source, `a9313d4f...`, passed in 8.0 seconds and its `ModelClosure`
consumer `941cbbd1...` in 6.3 seconds in
`remote-4ab8ba09754a449ba93cf6f707d08fbb`. The upper generator consumer then
failed at two missing instance binders, a separate ordinary source error.
These existing incremental results use unchanged toolchain and budgets;
they establish neither a controlled speedup nor the full arbitrary-base
projective-line endpoint. No extra benchmark or replay was run.

## Preserve local arrows and the final factorization witness

The private PBC
[global constant-factorization producer](../../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/FiniteCogenerators/Global/ConstantFactorization.lean)
also repeatedly exhausted the default 200000-heartbeat `whnf` budget.
Abstract local-stage witnesses alone did not close its concrete affine/gluing
consumer. The successful local-stage helper retains whole original functors,
objects, arrows and equations. Its concrete caller names the original
restricted coefficient and arrow, absorbs inverse image into the whole
functor, and specializes the remaining helper functor to the identity.

The final producer then passes an explicitly typed original open cover,
actual finite target, whole original `Over` comparison and actual local-factor
family to one opaque private theorem. That theorem performs the gluing and
constructs the literal finite-factorization witness, without asking the final
geometric consumer to normalize its complete existential body again. No new
finite-normalization or final-factorization premise is introduced.

The unchanged local-stage source `f9644b55...` passed
`remote-b64b8389ddbf43d18830d3b63cc27d6e`. Repaired constant-factorization
source `1c7853a72dc4ecd38ca43cb44a6b8467244cc21b5ba98f757bb301c4cb30126a`
passed its frontend in `remote-0aaf8c22b7024ac493af6cae40371111` (51 seconds).
The final Global consumer `317122f4...` subsequently passed
`remote-78ad06bad7da4473b43ab7c8fdbebad7`. These successive coupled repairs
establish the recorded producer coverage, not a controlled speedup or a
unique attribution of compiler cost. No additional replay, benchmark or
budget increase was needed.


## Share the original rectangle and fix group evaluation types

The private [GeometricFibreTransfer](../../Aglib/AlgebraicGeometry/EtaleCohomology/Stalk/GeometricFibreTransfer.lean)
consumer combines original cohomology-square transfer, its bijectivity and
the actual pointed-neighborhood rectangle. Abstract map families alone left
native conversion at the public boundary: source `83b144fa...` failed two
kernel checks in `remote-a6ae5a25...`. Sharing the transfer constructor closed
bijectivity, but the literal native rectangle in `86898d7d...` still timed out
in `remote-d86661e4...`. These observations do not isolate a unique cause of
kernel cost.

The accepted construction shares one public regular transfer constructor
between the generic producer and geometric consumer, and one public regular
predicate for the exact rectangle. The producer proves that predicate before
native specialization. Its scalar evaluation uses an abstract helper with
four explicitly typed `AddCommGrpCat` maps, applied before specializing to
cohomology. A generic `ConcreteCategory.congr_hom` evaluation had instead
exhausted `isDefEq` at the ordinary 200000-heartbeat limit in source
`f21bf9b8...`, `remote-4f7f8b90...`. The typed helper retains all four original
maps, coefficient isomorphisms, equations, hypotheses and cohomology universe.
It introduces no proper-base-change premise.

Final source `2f6b56168f7c87dc8fb8428357e11c537668a8d9ac6eb2f4c9b792f7caca0f49`
passed in 126 seconds in `remote-44ba09003b46423baacefbb5e45c9d0c`, source
snapshot `1e8592f0c827905be3cf7f594ff1f9d02f4e62a6ca59b4ad819937a66e18c511`.
The run used Lean 4.34.1, the pinned Mathlib and unchanged options and budgets.
The exact source, failed inputs and ordinary compiler logs remain with the
mainline task. This is compiler closure of the transfer and rectangle, not
a controlled speedup or completion of the original common-point exchange
or general PBC. No additional benchmark or replay was run.


## Return the whole standard bounded target test

The private [TargetLocality](../../Aglib/AlgebraicGeometry/EtaleCohomology/Proper/Universal/TargetLocality.lean)
consumer extends original bounded proper exchange from every affine spectrum
to arbitrary targets. Its public premise is the actual `boundedBaseChange n p`
for each proper map to a spectrum, and its conclusion is that same property
for the original proper map. No Noetherian, coefficient-order or uniform
geometric bound is added. The original four models remain independent in the
internal exchange proof; the native bounded predicate uses its original
standard models.

First repair actual typing errors: applying the affine provider had prematurely
specialized the implicit Cartesian objects. Introducing the complete square
before application, and retaining the full property in a typed `Eq.mp` transport
with `@hChart`, cleared those errors. In source
`0e494d7bbad1b930f4a9f2698e43b12174b2f655c252c120f6bff250fe89272e`,
all private chart/stalk steps then checked, but the public assembly had a kernel
`deterministic timeout` in `remote-c219cb9a852644a5a00c70af9d7f2361`
(160 reported module seconds).

Completing the entire original `IsIso` argument over four variable derived
models was insufficient at the public standard specialization. Source
`e660a87f894fd78034ac4682b9ec1da09da6bc441d695cfe2f24b31b8af444eb`
still failed the public theorem in
`remote-ee362f5f1f3947c6bbea9a22de39ecd0` (158 seconds). Adding a typed actual
exchange component and moving its canonical substitution into an abstract
adapter also left the public boundary failing: source
`e022e85baa40823a66bb6398fc78bfe194998dbc0963bc0ca2816d243573729a`,
`remote-bb7a35ad1dbf4197a3d17dd08aa1f809` (154 seconds). That result was
recovered after a transport interruption; compilation was not rerun.

The accepted version returns the exact regular
`boundedExchange n f f' g g' H.w.symm` from a complete private factory.
That factory fixes the four original standard levels and instances explicitly,
then supplies the actual component and its canonical equality to the abstract
producer. The component's underived sheaf-Hom carrier alone does not constrain
the four derived-model universes. The public `boundedBaseChange` theorem
introduces only the Cartesian square and consumes the whole factory, so its
producer and consumer share the same native quantified predicate head.
The actual ordinary/derived maps, chart restrictions, point/stalk unit,
Cartesian equation, coefficient and killed condition are retained.

Final source
`2b3610dcbe0952b2230eb3b21ec405afe0fa737ae0ddbffe2435cfbf7a30f6f6`
passed in 6.8 reported module seconds in
`remote-78fd87b3994849258cb6600228176b28`, source snapshot
`53cce8407c942401e8aa3dcd6e3d8a602c2fd34ba32bf03bd969e377a2a48f56`.
The closed batch had three frontends: this module passed, while the original
neighborhood and conditional common-point comparison failed. It is not a
successful final PBC build. Lean 4.34.1, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, the ordinary 200000-heartbeat
budget, jobs 16, threads 2, per-Lean heap ceiling 12800 MiB and global
RSS admission ceiling 110592 MiB were unchanged; there was no OOM. Full failed inputs and ordinary compiler logs are retained
with the mainline task under `universal/notes/`.

This is a combined boundary and explicit-model repair. The observations do not
isolate either change as the unique cause, provide a controlled speedup ratio,
or close the remaining common-point and full proper-base-change consumers.
No extra probe, profiling, replay or downstream check was run.

## Construct the chart exchange from its whole coefficient family

This case concerns private `Stalk/ChartExchangeMaps.lean`, with Lean 4.34.1
(commit `5045d0056413266e57c625dcd7c365b10e377c52`) and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The standard 200000 heartbeat
budget and admitted remote profile (16 frontends, two threads each, 12800 MiB
per compiler, 110592 MiB pool ceiling) are unchanged. The four original
`HasDerivedCategory` data records and their universes remain independent.

For an etale chart U of S and f : X -> S, write P for the original higher
direct image, Q for chart inverse image followed by chart higher direct image,
and alpha : P >> inverseImage(U.hom) -> Q for the original higher exchange.
Etale base change proves this whole alpha invertible. The required chart map
is exactly inverse original evaluation followed by global sections of
alpha.app F. The native map and its constructor equation, original-factor
equation and IsIso theorem must all retain these factors.

### Recorded failed boundaries

A generic constructor `chartSectionMapOfHom Gamma E beta`, with generic
composition and IsIso laws, did not close its native original-factor and
invertibility bridges. The following native attempts also failed:

- Focused regular map, source
  `37227288a12ce47f05742fccea9570ea07dc1c93f5ed044a46200e3581ffe90a`:
  kernel failures at the native equations in `remote-337df53f...`.
- Native map changed to an abbreviation, source
  `746c029d98beb5401c3e278bd825913b4bf1e2db7c4a2b874aa617a182064e38`:
  the same native failures in `remote-dbe460e0...`.
- Direct native reflexivity, source
  `9f64fbc7f02886828fe98d1fdcbf177d34cae54ce227e0a79212a10ccca6d697`:
  original-factor bridge still fails in `remote-0288f2fd...`.
- One-element hom extensionality, source
  `7c1f51698bef9c5d7a36bd92c793234101799d2b22b38975399162b966f1c2a6`:
  bridge still fails in `remote-0c1f1360...`.
- A single map-and-laws witness over Gamma, E and beta, source
  `efd64a9ddc5f7d2d04cb1eea4881789f196cf44aa07296979e7a4b7aeb8b118a`:
  native opaque initializer fails in `remote-50ecadc6...`; subsequent unknown
  initializer errors are cascades.
- A scheme/sheaf-variable witness constructing E internally, with explicit
  scheme endpoints for inverse image and higher direct image, source
  `e2d166f347cc73ae2ae35ab297d26757c8544d8f2a14bc07cc981463db3ab37d`:
  native initializer still fails at line 114 in `remote-8f8bada5...`.

The earlier bounded stack observation `978eca66...` locates final inferred-type
comparison for an older native equation. It does not locate the later opaque
initializer's failing kernel phase. The actual expensive expression pair was
not recovered. Abbreviation-hint facts do not establish a unique cause.

Valid command-only Meta inspections `0fc1ed68...` and `622ac4fe...` report the
actual application arguments with recovery disabled and no target declaration.
The latter matches the S/U/L/M type hashes but exposes a component source
written as a composite functor applied to F on one side and nested object
applications on the other. Their different functor-domain parameters explain
the reported S/X nodes; this is not a mathematical scheme mismatch. The IsIso
argument also has differing hash hints, but the walk reaches its difference
cap before inspecting that pair. Hashes do not certify identity, and these
reports are not native kernel-comparison traces. The recovered-value reports
from `fa17aa13...` are rejected evidence.

### Accepted provider construction

Replace the scalar-component witness interface with a witness over the actual
coefficient functors P and Q, their whole alpha, and F. Its generic producer
constructs the original evaluation and alpha.app F internally, while these
functors remain variables, and derives component invertibility from the whole
IsIso alpha. The native initializer supplies the original higher-exchange
transformation and its etale invertibility proof, explicitly retaining all
four original models. The same witness yields the map and both exact factor
equations. No extra opaque layer or additional mathematical premise is added.

Provider source
`52cfb38d2f8a37f989f3ba8c804c4b2c33698b578745973bcdfe7d8045f74320`
compiled as an ordinary native Lake module in `remote-12d681cd...` in 23 seconds,
source basis
`b0e97845f2df43a5e9e0b226e28dd2226152b7dc3f1071f6a123270fe8b542cd`.
This covers native specialization, public map, constructor equation, literal
original-factor equation and invertibility, not merely an abstract helper.
Public native definitions/statements, consumer formulas and options are
unchanged from the preceding candidate. No additional benchmark, replay or
separate client check was run.

The actual `BaseChangeNeighborhoodGerms` consumer source
`4c4211caf23a5436177030fa24042f4fc8f37011cebbfc31de218d6d6a43dd9f`
fails in the same graph after 420 seconds: primary kernel timeouts at
`originalChartSection_hom:276` and `higherBaseChangeMap_sectionChart_square:445`.
Unknown helpers at lines 302 and 533 are cascades. The remaining CH and section
square still require their own native specialization repairs. This records a
complete provider pass and its actual consumer limit; it does not transfer
that pass to the full neighborhood equation. The independent D branch in the
same graph retains its own results.

Exact source packets, capture records, bounded observation reports, compiler
events and receipts are retained under the mainline task's
`universal/notes/` and `universal/remote-runs/`. Run abbreviations above refer
to their unique retained full IDs. The provider pass removes the recorded
budget failure at this interface; it does not establish a controlled speedup,
a unique kernel cause, or proper base change.

A subsequent CH-only proof-body trial first applies extensionality at the
accepted native endpoints, then rewrites the scalar constructor and applies
the original scalar CH law. Consumer candidate
`df31b72761d64191fd4d5de91db95800979c0f4657fd88632066d62399384f29`,
checked through isolated native prefix
`8162a1508a44fc50d7a8b573d9c9403a78cd0d3cbe65987f8616a17be5b0ba95`,
still fails kernel checking at line 276 in `remote-3d549296...`. This does not
reopen or invalidate the accepted chart provider. It shows that a smaller
extensionality-first consumer proof alone is insufficient at the next boundary.

## Evaluate the raw group rectangle before specializing cohomology objects

This continuation concerns private `Stalk/GeometricComparisonEquation.lean`
on Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`,
and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The admitted
remote profile remains 16 frontends, two threads per compiler, 12800 MiB
per compiler and a 110592 MiB pool ceiling. Generic helpers and native whole
map equations use the standard 200000 heartbeats; the isolated scalar proof
retains the existing declaration-local 500000 allowance. No global budget or
coefficient/model universe is changed.

The required original neighborhood rectangle is `T >> vRaw = uRaw >> dRaw`
in `AddCommGrpCat.{e}`. Here T is the original cohomology transfer with its
inverse-square coefficient; uRaw and vRaw are the original relative transfers
on the two original pointed maps, and dRaw is the original geometric-fibre
cohomology transfer. A generic value equation converts the relative transfer
at `Over.mk` to the actual triangle constructor while the schemes, maps and
Ext data are variables. The native whole-map helper uses that value equation,
the existing native triangle rectangle, and finite map congruences. It retains
all raw operands and the original coefficient square.

### Boundaries that did not close the consumer

Direct use of the generic square-triangle scalar law at the native scheme,
point and cohomology objects still timed out during kernel checking. The
isolated `cd2bfaa...` input failed at line 160 in `remote-1b5d48a...`.
An explicit literal Eq/H output carrier (`2b0c64f...`, `remote-28b548a...`)
and combining that literal carrier with the already-closed native triangle
predicate (`a048f2f...`,
`remote-20111351...`) also failed at that native scalar boundary. The latter
failure does not invalidate the complete provider
`GeometricFibreTransfer` at
`b8e3d62c0300732c973e85798ee96fcc4973d10e5ac60a1ef20c7e3565b62796`,
which compiled with the standard budget in `remote-651591e5...`.

An exact RAW whole-map equation, isolated source
`8737f1319eb1bf985208d6da2a0748d24ec887c8806683a34a2d866024e92109`,
passed in 90.95 seconds in `remote-1230ef7ef16b4f51b638420383ffda76`.
That diagnostic retained a local 500000 allowance on its native whole helper;
the later accepted isolated consumer keeps the whole helper at the default.
An earlier attempt (`7981907655...`) had a real typeclass-search failure on
the generic Over.mk bridge; supplying its original Ext dictionaries explicitly
fixed that error. It was not a successful proof before this repair.

Evaluating the completed raw equation directly in the native consumer still
failed: isolated `3e4182e...` had an elaborator whnf timeout at line 245 in
`remote-9f26b921...`. After simplifying composition, isolated `5bdca2de...`
reported an elaborator type mismatch at line 265 in `remote-e051697e...`,
even though pretty-printed types looked identical. These were elaboration
failures; they do not identify a failing native kernel conversion.

The guarded independent expression report for source `57956185...` in
`remote-ac6698f0f7de427baceb07b965ef54cc` inferred the actual local hs without
an expected type. It exposed concrete-carrier/applied-family representation
heads in the goal and bare `Sheaf.H`/`AddMonoidHom` heads in the simplified
hs. Recovery was disabled, sorry and metavariables were rejected, and the
probe created no target declaration. It is an expression observation, not
proof closure or a unique diagnosis of kernel cost. No FC/CC instance was
replaced or overridden.

### Accepted abstraction boundary and actual scope

A private `rawGroupSquare_apply` takes variable objects A, B, C, D in the
actual `AddCommGrpCat.{e}`, four maps r, v, u, s, and their whole equation
`r >> v = u >> s`. Its conclusion is the ordinary concrete-coercion equation
`v (r x) = s (u x)`. `ConcreteCategory.congr_hom` and composition evaluation
are proved there before substituting the native cohomology objects. The
native scalar supplies the four original raw maps and the exact raw-map
rectangle. It neither reconstructs the triangle matrix nor simplifies a
native coerced composition.

Isolated source
`2784d4a706bb5086d3ceb4f0dc56dcf61b3cc3095a010c5308c52fd60503821c`
passed as an ordinary native frontend in 131.289 seconds in
`remote-d8c97df6969b4ab1855890660a8fc8b9`, source basis
`4cb4b7403d12e9bfc4fc7daea19216408cf065450b047926ac83b0499dbcbbea`.
Its exact input manifest, original Lake-generated setup, empty compiler leaf
log and receipt are retained in the task's `universal/remote-runs/` directory.
This covers the generic evaluator, default-budget whole-map bridge and its
actual native scalar consumer. It does not by itself close the later stalk
representative assembly or proper base change.

Full module candidate
`ee3d48dbc608450d900b89160971cd8566e62a54b24ca304442b91ad82348b24`
uses this scalar proof inside the original pointwise assembly. The complete
ordinary Lake module build passed in
`remote-d45fbc3f951247f7be8c3b69813760a6`, source basis
`d5af38541b2338cb62ce944f20ee2d32755b23700441e36fc3f09d785a101f76`.
Lake reported 357 module seconds; the managed command elapsed 361.10 seconds.
Exactly one frontend ran, with no diagnostic or OOM. This includes the full
original representative assembly and original-model wrappers, beyond the
isolated scalar. The N neighborhood equation and downstream exchange/proper
consumers remain open. No replay, separate downstream/client check, new
coefficient premise or universe identification was used. Source packets and
source-correspondence notes are retained under the mainline task's
`universal/notes/pbc-native-fixed-inputs/D_raw_group_eval/`.

## Transport the actual chart exchange value before projecting its scalar law

This continues the chart-family case on the same Lean 4.34.1 / Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` pins and admitted remote profile.
The provider `52cfb38d...` remains frozen. The target is the actual private
`originalChartSection_hom` additive-map equation in
`BaseChangeNeighborhoodGerms`; the native chart, original resolution map,
cohomology comparison and four independent derived-model records are retained.
All new helpers and this native CH target use the default 200000 heartbeats.

The old `df31b727...` extensionality-first attempt failed as recorded above.
Further scalar composition/carrier normalization in native prefix
`5a52a12193de55d286e518198dbe191deecc1c3a534f13a2a64348a610af45de`
still timed out during kernel checking in `remote-9f26b921...`. The guarded
law-input report `bf7f0a7e...` in `remote-ac6698f0...` located a difference in
the supplied scalar law before source-function evaluation. The refined
extraction `2ed4425558dcdeaff893fd99d91c6f85981f473923719c3ff57094bca509de65`
in `remote-fede953915a14565811be92f6709a04b` peels the exact mapped component
and whole `higherBaseChangeMap` from the expected and primitive law types.
It reports literal U.left/hBase on the consumer side and
`(Id Scheme).obj U.left` with the actual
`baseChangeChartSections_targetIdentityHasDerivedCategory S U hBase` alias on
the primitive side. The other three model arguments are the same local data
variables. Long scheme/typeclass subtrees are explicitly clipped; the model
records themselves were printed. There was exactly the intended completion
error, no target declaration, no recovered value and no equality/kernel claim.

The repair proves a named F-free value equality of those two original whole
transformations, with their original explicit levels, actual records and
pullback condition terms. Extend the same variable-functor carrier lemma to
take both whole values and their proved equality. It uses `NatTrans.congr_app`
and Gamma congruence only while the functors and transformations remain
variables; it then applies the primitive scalar law in its actual projection
presentation. The native CH proof supplies the actual value equality and
unchanged original scalar law. No provider rewrite, standard-model replacement,
extra opaque record, new public premise or universe identification is made.

Initial complete native prefix
`90aed4e6d1b3e66d0763aefa8413bf01a10ce063e34a8c3c03f0b6d129ab600f`
had ordinary errors in `remote-efd589b492924cdb87c5b90a1107fc78`:
the value lemma automatically included three unused Ext section instances,
and its manually ordered universe invocation consequently assigned a derived
model level to the wrong slot, followed by a typeclass-search cascade. No
kernel timeout was reported there. Do not interpret that failed frontend as
successful bridge or CH closure. Removing those unused instances with `omit`
and allowing the four separately typed original model arguments to infer the
helper's levels changes only two source lines; both whole transformation
expressions keep their explicit original universes.

Corrected complete native prefix
`cfe977563696c6705ff4338f38ae67305a5b1985bc8fd981c813a0f5a8a415dd`
passes in 77.342 frontend seconds in
`remote-a0956fd37add468aab9f6d8ff9a7f44b`, source basis
`d5af38541b2338cb62ce944f20ee2d32755b23700441e36fc3f09d785a101f76`.
The managed command took 82.517 seconds; one frontend ran, the leaf log is
empty and no OOM occurred. This includes the generic transport, exact native
whole-value equality and original CH consumer, not just the F-free helper.
There was no separate generic-only check, benchmark, replay or client test.

Only its byte-identical prefix was admitted to the full private N source,
now `ef833f0b80d8f68dc8565171a08a1442ca293615ab466c25c21756ef754e4436`.
The complete original tail from `fibreProductChartSection_hom` onward is kept
at the original4c source, including the still-unclosed section square. Its
SHA256 is `ed89eeddd00598e785f4e2b44ef558f90f5f876bc739621142c7d42aa2559df4`.
Full N and its downstream PBC consumers remain uncompiled. The exact fixed
inputs, failed/corrected prefix pair, metadata logs and original run records
are retained under the mainline task's `universal/notes/` and
`universal/remote-runs/`. This establishes an effective representation repair
for the actual CH boundary, not a unique kernel-cost diagnosis or general PBC.
