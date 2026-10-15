# Cohomology development plan

The current development targets canonical affine module base change and flat
base change with arbitrary quasicoherent coefficients, first for separated
schemes and then for qcqs morphisms. Projective finiteness, Serre duality and
proper cohomology and base change develop alongside that route, sharing the
same native objects and lower prerequisites.

The starting source is Aglib `bdee1b16373d721dbec6f93fae39690c4f8c36ae`,
Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Work is isolated on `codex/cohomology-foundations`. Existing theorem-family
inputs remain explicit until the complete quantified statement has a proof.

## Mathematical targets and acceptance

1. **Affine module base change.** For affine `f : X ⟶ S`, quasicoherent
   `M : X.Modules` and arbitrary `g : T ⟶ S`, prove that the existing
   `Scheme.Modules.moduleBaseChangeMap f g M` is invertible. No flatness,
   finiteness or Noetherian hypothesis is admitted. Identify its affine tensor
   formula and adjunction-unit/counit normalization; supply the existing
   `AffineModuleBaseChange` family without an additional mathematical input.
2. **Separated flat base change.** For a quasi-compact separated morphism `f`,
   flat `g` and arbitrary quasicoherent `M`, prove canonical base change in
   every nonnegative degree. First work over affine bases `Spec A`, `Spec B`,
   with arbitrary commutative rings and a flat map `A → B`. Preserve the actual
   `Sheaf.H`, structural scalar action, coefficient naturality and canonical
   tensor/geometric map. Recover the existing field/structure-sheaf theorem as
   a specialization, without assuming cohomological finiteness.
3. **Qcqs flat base change.** Extend the preceding theorem to qcqs `f` using
   finite affine unions and Mayer–Vietoris. Supply quasicoherence and affine
   computation of the actual higher direct images. Relate the resulting
   isomorphism to the existing `derivedFlatBaseChangeMap` on bounded-below
   complexes with quasicoherent cohomology; arbitrary module complexes are
   not covered merely by constructing that map.
4. **Projective finiteness.** For Noetherian `A`, projective `X → Spec A` and
   coherent `M`, prove `Module.Finite A Hⁿ(X,M)` for every `n`. Use Mathlib's
   actual `Proj`, standard affine charts, actual twisting module sheaves and
   their Cech cohomology. Establish finite twist presentations and coherence
   of kernels, then use long exact sequences and descending degree induction.
   Prove Serre vanishing with the same infrastructure. Extend to coherence of
   higher direct images over locally Noetherian bases by affine localization.
5. **Proper finiteness.** Extend projective finiteness through Chow's lemma,
   coherent devissage/Noetherian induction and Leray comparisons. The target is
   coherence of `Rⁿf_* M` for proper `f` over a locally Noetherian base, hence
   the complete existing `ProperModuleCohomologyFinite` family over fields.
   A projective special case is useful progress but does not discharge it.
6. **Projective, then proper cohomology and base change.** First let `A` be Noetherian,
   `X → Spec A` projective and `M` coherent and flat over `A`. Construct a bounded
   finite-projective complex computing the cohomology after every `A → B`,
   and identify the canonical derived base-change map. This target includes
   upper semicontinuity of every fibre-cohomology dimension, local constancy
   of the Euler characteristic, Grauert's theorem with its precise
   reduced-base hypotheses, pointwise surjectivity/base-change criteria and
   local-freeness criteria for individual higher direct images. Constant
   fibre dimensions alone on a nonreduced base do not supply local freeness.

   Perfect **direct image** `Rf_*` is a separate explicit endpoint: proper
   perfect morphisms over a Noetherian base preserve perfect complexes;
   more generally retain the
   relative-perfectness hypotheses needed for a perfect direct image. Derived
   base change along a classical fibre square retains Tor independence, unless
   the coefficient-flat situation proves the needed Tor vanishing. Arbitrary
   base change for an arbitrary perfect coefficient cannot be inferred merely
   from projectivity or properness. The flat-coefficient complex model above
   proves its own all-base-change assertion on the actual ordinary fibre
   product.

   Prove these geometric versions for projective morphisms before taking on
   the Chow/devissage extension to general proper morphisms. For arbitrary bases,
   retain proper finite presentation and a finitely presented relatively flat
   coefficient; supply the needed approximation or relative-perfectness
   theorem before claiming the full `LocalFreeCohomologyBaseChange` family.
7. **Serre duality.** Start with projective space: compute twists, construct
   trace and the Yoneda pairing, and prove duality and naturality. Extend to
   smooth projective schemes over a field, of pure dimension `d`, and coherent `M`, with
   `Hⁱ(X,M)ᵛ ≃ Ext^(d-i)(M,ω)` for `0 ≤ i ≤ d`. Finite locally free
   coefficients give the dual-tensor cohomology formula. Prove the comparison
   between O-linear Ext and additive `Sheaf.H`. Identifying `ω` with the top
   exterior power of differentials also needs the actual smooth differential
   rank theorem. General proper, possibly singular schemes require a
   dualizing complex and remain a separate, explicit extension target.

The projective/proper base-change suite is accepted only when its geometric
endpoints are available on the original objects, with the following checks.

| Endpoint | Required original interface and hypotheses |
| --- | --- |
| Coherent direct images | Actual `Rⁱf_* M`, projective/proper over a locally Noetherian base and coherent `M` |
| Flat base change | The original tensor/geometric mate, arbitrary quasicoherent coefficients, qcqs `f` and flat base change |
| Flat-coefficient base change | A universal bounded finite-projective model under the precise Noetherian/finite-presentation and relative-flatness conditions |
| Semicontinuity | Upper semicontinuity of `s ↦ dim κ(s) Hⁱ(Xₛ,Mₛ)` and locally constant alternating sum, derived from that actual model |
| Grauert | Local freeness and arbitrary base-change compatibility, with reducedness or the stronger pointwise criterion retained as required |
| Pointwise criterion | Surjectivity of the original residue-field base-change map, its neighbourhood consequence, and the adjacent-degree local-freeness criterion |
| Perfect direct image | Actual `Rf_* E` perfect under proper-perfect/Noetherian or proper-flat-finite-presentation/relative-perfect hypotheses |
| Compatibility | Coefficient maps, open restriction, composition of base changes, and comparison with the existing derived map |

A lower finite-complex theorem is a prerequisite for this table, not a
replacement for a geometric endpoint. The first implementation may use
projective `f`; the extension from projective to proper remains explicit.

## Shared prerequisites and proof routes

The affine section/tilde equivalence and canonical affine tensor comparison
feed both module base change and Cech coefficient base change. Structural
scalars must be generalized below the field specializations, preserving their
existing definitions by explicit comparisons rather than parallel cohomology.

The finite-family coefficient comparison already avoids any assumption that
tensor preserves infinite products. The current full-tuple Cech complex is
unbounded even for a finite cover. Bounded ordered/alternating Cech comparison,
or a proved finite-cover cohomological bound via Mayer–Vietoris, must precede
the finite-amplitude arguments. Its terms are not generally finite over the
base ring. Proper finiteness and finite Tor amplitude, rather than finite
cover size alone, provide the finite-projective model.

The selected bounded-flat route retains the full native tuple complex. For
relatively flat coefficients its terms are flat over the base, and the
finite-cover cohomological bound holds after every base-ring map. Applying
this also to square-zero extensions proves the needed tensor exactness for
every base module. Purity and kernel-flatness then prove that the terminal
cycle of a good truncation is flat. An exact unbounded tail of flat modules
alone is insufficient for that step. Noetherian cohomological finiteness and
the resulting finite Tor amplitude supply the finite-projective replacement.

Projective geometry uses general arbitrary-dimensional constructions; curve
degree, genus, Riemann–Roch and K/G/Q/S applications stay downstream. New
constructions extend native mathematical namespaces with precise lower imports.
Generic complex/perfectness lemmas belong below scheme cohomology.

## Derived-method review

New proofs are paused for this review. The current source already uses
native bounded-below derived categories, actual derived units and genuine
finite-projective models. The recommended next architecture adds focused
derived bridges to those constructions; a full unbounded duality theory
has substantially more prerequisites in the pinned libraries.

For flat base change, retain the proved affine injective-resolution
producer. Assemble open locality using exact restriction, its preservation
of injectives, the original ordinary restriction isomorphism and the native
derived-composition isomorphisms. Use the installed
`derivedFlatBaseChangeMap` as the sole canonical derived map. Its current
source constructs the map and its unit equation, but does not prove it
invertible. Its homology on quasicoherent single objects still needs
identification with the proved scalar cohomology map. A later finite
Postnikov argument can extend this to bounded-below complexes with
quasicoherent cohomology. Injective or Godement terms must not be treated
as quasicoherent merely from their acyclicity.

For the perfect-direct-image object, exactness of tilde permits direct
transport of the existing derived global-section isomorphism through
`tilde.rightDerivedFunctorPlus`, using its invertible native units. This
can remove K-projective representative selection from the object-level
source and arbitrary-base-change constructions. Existing actual chain-map
versions remain useful for their explicit normalization formulas. This is
a proposed simplification; the present compiled implementation is retained.
For arbitrary perfect coefficients, relative finite Tor amplitude,
derived tensor/pullback and the corresponding projection formula still
need native interfaces. General nonflat derived tensor does not preserve
D+: it may have unbounded negative homology. A proposed interface must
retain appropriate bounded-above, perfect or finite-Tor restrictions.

For general smooth projective Serre duality, the smaller candidate route
uses only the right adjoint of a closed immersion and its bounded-below
right-derived functor. If `i : X → P^N` is regular of codimension `c`, the
required calculation is `Ri!(omega_P) ≅ omega_X[-c]`. Then the derived
adjunction identifies actual `Ext_X^j(M,omega_X)` with
`Ext_P^(j+c)(i_*M,omega_P)`, so the existing projective-space duality and
original pushforward cohomology comparison give the desired result.
For coherent single objects this does not first require extending
projective-space Serre duality to every bounded coherent complex.

Exact closed-immersion pushforward, native D+ right derivation and the
generic `Adjunction.derived` exist. The actual closed-immersion right
adjoint and its D+ specialization still need construction. The current
`Adjunction.extEquiv` assumes both ordinary functors exact and cannot be
used for a merely left-exact right adjoint. Major additional geometric
prerequisites are regular embeddings, Koszul calculations and the
conormal/determinant identification with top differential forms.
`SmoothDifferentialRank` still has no supplier. Smooth local-ring
regularity and dimension are already proved and should be reused.
See [closed-immersion duality](https://stacks.math.columbia.edu/tag/0A9X)
and the [regular-immersion calculation](https://stacks.math.columbia.edu/tag/0BR0).

General proper coherent finiteness remains an independent geometric
obligation. The abstract perfect-image theorem first uses coherent proper
direct images and then finite relative Tor dimension; it does not eliminate
the former proof. The existing native derived-pushforward composition
already supplies the Leray comparison needed by the Chow/devissage route.
See [proper perfect-image construction](https://stacks.math.columbia.edu/tag/08EV)
and the [finite-complex flat-coefficient proof](https://stacks.math.columbia.edu/tag/07VJ).
The full right-adjoint construction via unbounded D(QCoh), compact
generation and representability is a larger separate project; see
[Stacks 48.3.1](https://stacks.math.columbia.edu/tag/0A9E).

## Parallel ownership

| Workstream | Initial write ownership | Immediate product |
| --- | --- | --- |
| Affine base change | `Modules/BaseChange/Affine.lean` and focused helper leaves under `Modules/BaseChange/Affine/`; that family's README | Canonical affine base-change theorem and its retained-family supplier |
| Flat cohomology and integration | General-ring scalar/cohomology leaves; general-coefficient base-change leaves; `doc/`; aggregate enrollment and shared interface documentation | Separated, then qcqs flat base change; canonical-map integration |
| Projective and duality | New leaves under `AlgebraicGeometry/ProjectiveSpace/`, `Cohomology/Projective/`, `Cohomology/Duality/`; their family guides | Actual projective/twist/Cech results, then finiteness and trace/duality |
| Proper base change | New generic leaves under `Algebra/Homology/FiniteProjective/`, new `Cohomology/Proper/` leaves and their guides | Finite-complex algebra and relative-flat/base-change prerequisites, then the proper endpoints |

Paths above are relative to `Aglib/AlgebraicGeometry/` unless a full family is
given. Owners request additional existing files before modifying them. Only the
integrator changes common facades, `doc/INTERFACES.md`, `doc/README.md` and this
plan. No worker changes dependency pins or Git state. Small proved prerequisites
are integrated as soon as they have their own precise statement and consumer;
an intermediate result never changes an endpoint's completion status.

## Incremental verification

- Edit one Lean leaf, compile it, repair diagnostics, and only then advance to
  the next leaf. Preserve all compatible copied build artifacts.
- Mathematical/source work runs in parallel; Lean frontends run through one
  shared build lock. Each guarded invocation names one explicit module or probe.
- Use `scripts/build_serial.py` for the changed leaf and strictly necessary
  prerequisites. If a target unexpectedly expands into a broad rebuild, stop
  and inspect cache identity/imports instead of allowing it to continue.
- Do not run `lake build Aglib`, `lake build AglibTest`, an unqualified build,
  the full integration script, cache cleaning, or a dependency upgrade.
- Use meaningful focused consumers to check canonical-map normalization,
  public visibility, generality and scalar compatibility. Run applicable
  source/enrollment/style checks on settled files without a full library build.
- Update the owning family guide with proved declarations, exact conditions,
  canonical maps and remaining inputs. Record successful commands and relevant
  failures once; do not repeat a passed build without changed inputs.
- No placeholders, custom axioms, circular theorem-family inputs, or weakened
  endpoints. Kernel acceptance of a leaf is distinct from completing a retained
  mathematical family.

## Primary mathematical references

- [Stacks 30.5.1–2](https://stacks.math.columbia.edu/tag/02KE): affine and flat base change.
- [Stacks 30.8](https://stacks.math.columbia.edu/tag/01XS): projective-space cohomology.
- [Stacks 30.16](https://stacks.math.columbia.edu/tag/0B5S): projective finiteness and vanishing.
- [Stacks 30.19](https://stacks.math.columbia.edu/tag/02O3): proper coherent direct images.
- [Stacks 30.22](https://stacks.math.columbia.edu/tag/07VJ): proper flat-coefficient base change.
- [Stacks 36.30.4](https://stacks.math.columbia.edu/tag/0B91): arbitrary-base perfect direct images.
- [Stacks 37.61.13](https://stacks.math.columbia.edu/tag/0B6G): proper perfect direct images over a Noetherian base.
- [Stacks 36.35.10](https://stacks.math.columbia.edu/tag/0DJT): flat proper finite-presentation and relative-perfect direct images.
- [Stacks 36.32.4](https://stacks.math.columbia.edu/tag/0D4E): fibre cohomology and finite-complex criteria.
- [Stacks 36.22](https://stacks.math.columbia.edu/tag/08ET): Tor-independent derived base change.
- [Stacks 48.27](https://stacks.math.columbia.edu/tag/0FVU): proper-field duality and trace.

## Current status

The affine endpoint is proved: `Scheme.Modules.moduleBaseChangeMap_isIso`
has only affine `f` and quasicoherent coefficients as premises, and
`affineModuleBaseChange` supplies the existing full quantified family. Its
focused leaf and final-import consumer passed, and its axiom inspection
reports only `propext`, `Classical.choice` and `Quot.sound`.

The arbitrary-ring scalar action on actual `Sheaf.H`, linear Cech computation
in degree zero and positive degrees, and geometric coefficient maps have
passed focused compilation. The degree-zero comparison requires only sheaf
gluing and the actual open cover. Exactness of native scalar extension along
an arbitrary flat ring map is proved with independent carrier universes.
Generic degree-zero and geometric Cech comparisons have been extracted from
their field-specific owners while preserving their mathematical declarations.
The separated flat-base-change endpoint over spectra is proved in every
nonnegative degree: `moduleCohomologyBaseChangeMap_isIso_of_isSeparated` has
only quasi-compact separated `f`, flat `σ` and quasicoherent coefficients as
premises. Its original unit formula and equality with the actual Cech
transport are proved. A final-import consumer passed, including the literal
canonical map, all degrees and standard axioms only. The qcqs extension is
also proved in all degrees: `moduleCohomologyBaseChangeMap_isIso_of_quasiSeparated`
requires only quasi-compact quasi-separated `f`, flat `σ` and quasicoherent
coefficients. The supplied-cartesian-square version retains the original
unit and tensor map. The proof uses the actual open-restriction comparison,
native Mayer–Vietoris tensor ladder and compact-open induction; separated
compact intersections discharge every local invertibility premise.

The actual affine higher-direct-image computation and quasicoherence are
now proved for qcqs morphisms to a spectrum and arbitrary quasicoherent
coefficients. The comparison uses the original module injective resolution,
structural-ring global sections and the native tilde–Γ counit. The native
right-derived-functor/integer-resolution homology comparison is also proved.
Their independent consumers passed `1792107629222487000-15468` and
`1792108251788846000-25675`, with only the standard three axioms. Passage
to a general target and invertibility of the installed derived flat
base-change map remain separate obligations.

The first resolution comparison is proved: native global sections of the
original module injective resolution have homology linearly equivalent to
the unchanged additive `Sheaf.H` in every nonnegative degree. The comparison
retains the original Ext representative and is natural for resolution maps.
Its public consumer requires no local HasExt or colimit workaround.

The genuine module-linear Cech/resolution chain zigzag is also proved,
using the original module injective resolution and native augmentations.
It identifies the original integer Cech complex with the installed
derived global-sections object of the original module in degree zero.
The fully expanded forward map retains both actual augmentations, native
extension comparison and installed derived unit. Actual resolution lifts
give coefficient naturality. The original finite Cech inclusion composes
directly with this derived-object isomorphism; no cohomology-only inference
is used.

The projective branch has actual polynomial `Proj`, standard affine charts,
coordinate-ring polynomial equivalences, overlap transition units/cocycles,
actual invertible twisting sheaves for every integer, and a Cech computation
by original `Sheaf.H`. Homogeneous polynomials define actual global twist
sections; the coordinate powers prove global generation of every nonnegative
twist. The actual full-tuple twist Cech complex is now identified with the
native Laurent-coordinate tuple complex and its true coproduct of relative
simplex weight complexes. For every integer twist and every degree, actual
twist cohomology is finite free over the arbitrary structural base ring.
It vanishes away from degrees zero and the projective dimension; positive
cohomology vanishes for twists at least the negative projective dimension.
The dimension-zero case retains both possible degree-zero weight summands.
Finite coordinate types in the ring universe are related to `Fin (n + 1)`
by an explicit equivalence, with `ULift` giving the standard specialization.

Actual twist multiplication and its polynomial naturality are proved.
Every finite-type quasicoherent module on this projective space now has an
actual epimorphism from a finite coproduct of negative twists, surjective
on the original standard-chart sections. Over a Noetherian base its native
kernel short exact sequence has a finite-type quasicoherent kernel. The
descending induction is now complete: every original cohomology group of
a coherent module on polynomial projective `n`-space over a Noetherian ring
is finite over the literal structural base ring. A focused external consumer
checks all degrees and arbitrary universes using lifted finite coordinates.
An actual closed immersion into this projective space now gives the same
all-degree finiteness theorem for its coherent coefficients. The comparison
uses the original geometric cohomology map and the literal factorization of
the structural morphism; coherence of closed-immersion pushforward is proved
by the existing affine interface. Serre vanishing on projective space is
also proved: one bound works for every larger integer twist and every
positive degree. It uses the actual uniform twist presentation, exact
tensor, original long exact sequence and finite-cover vanishing bound.
The actual top trace is an isomorphism from `H^n(O(-n-1))` to the base
ring, with the original Laurent residue and sign, including dimension
zero. The canonical top Serre duality is also proved for every coherent
coefficient on polynomial projective space over a Noetherian commutative
ring: actual `Hom(M,O(-n-1))` identifies with the dual of original `H^n(M)`.
The forward map is exactly the original trace after the original cohomology
map. The proof uses the actual uniform two-step twist presentation and the
native exact-row diagram. Over a field the corresponding original pairing
is perfect. The public consumer passed `1792102835410169000-33277` with only
the standard three axioms. The full higher Ext form over a field is now
proved on polynomial projective space: for every complementary pair
`i+j=n`, the original Yoneda/residue pairing is perfect and supplies both
linear duality isomorphisms. Coefficient naturality, dimension zero,
finiteness of the actual Ext groups, vanishing above the projective
dimension and the signed boundary identity are explicit. Public consumers
passed `1792105679932958000-87897` and `1792106155567419000-95038`, using
only the standard three axioms. Duality for general projective schemes
and general proper dualizing complexes remain separate targets.

The canonical O-linear Ext/unit comparison with original additive cohomology
is now proved in every degree for arbitrary module sheaves on arbitrary
schemes. Its forward map is exact scalar forgetting on native Ext preceded
by the original integer-generator-one map. Degree-zero Hom, coefficient
naturality and Yoneda compatibility are explicit. The proof uses actual
flasque acyclicity of module injectives. Structural-ring linearity is now
proved for the original source-precomposition action on Ext and the original
coefficient action on cohomology. Its degree-zero normalization is exactly
evaluation of the original module morphism on the global section one.
The native long exact sequence is also linear over any specified structural
ring. Noetherian finite-generation transfer uses its actual coefficient and
connecting maps. The old field-linear exactness interfaces now delegate to
this generic implementation.

The proper branch has native finite-projective model base change, split cycle
sequences, canonical homology scalar-extension maps and an actual two-term
local-ring residue-homology/free-H0 criterion. A bounded finite-projective
complex with residue homology concentrated in degree zero is now proved
homotopy equivalent to a single finite-free module, and its original homology
base-change map is invertible for every ring map. A finite affine cover on a
separated scheme also gives the sharp vanishing bound for actual quasicoherent
`Sheaf.H`, using Mayer–Vietoris. Universal tensor exactness now proves
flatness of the actual terminal cycle. Native scalar extension preserves
the corresponding boundary kernel and commutes with the original good
truncation, retaining the actual inclusion and coefficient naturality,
without assuming the base-ring map flat. The actual finite-cover bound now
holds after every base-ring map, and its square-zero-algebra specialization
proves universal tensor exactness of the original Cech differentials. For
relatively flat quasicoherent coefficients, this gives flatness of the
original terminal cycle and every term of the bounded good truncation. Its
arbitrary-base-change isomorphism retains the original truncation inclusion
and ordinary pulled-back coefficient. The geometric integration
and proper endpoints remain in progress. These lower results do not
discharge proper finiteness or `LocalFreeCohomologyBaseChange`.

The generic finite-projective replacement is now proved. For a bounded
flat complex over a Noetherian ring with finite original homology, it
constructs a finite-projective complex in the same interval and an actual
quasi-isomorphism to the original complex. The same actual chain map
remains a quasi-isomorphism after every ring map, including larger-universe
target rings. The proof uses native finite-free homology covers, actual
mapping cones and truncations, and the native rotated-cone reassembly.
The geometric projective supplier is also proved. An actual closed projective
embedding, coherent coefficient and relative flatness supply one bounded
finite-projective model over the Noetherian base. Its actual comparison to
the original finite Cech complex stays a quasi-isomorphism after every ring
map. The same model computes the original cohomology of each ordinary pulled
coefficient and represents the installed native derived global sections by
the genuine Cech/injective-resolution chain zigzag. The native degreewise
mate is now identified with the original geometric cohomology base-change
map by a full linear square, including their distinct original carrier
universes. Invertibility and surjectivity transfer through these actual
comparisons. The installed derived-global-sections object is also computed
after every ring base change. Actual sheaf-valued perfect direct image is
also proved for this projective, coherent relatively flat coefficient.
The constructed strict finite locally free sheaf complex represents the
installed native `Rf_*` of the original coefficient in degree zero. Its
actual chain map is the tilde of the injective-resolution comparison
followed by the original tilde--Gamma counit, which is proved to be a
quasi-isomorphism. The same construction works after every ring map,
without Noetherianity or flatness of the new ring. The source and arbitrary
base-change public consumers passed `1792106876856067000-4795` and
`1792107141271240000-8810`, with only the standard three axioms. These
statements concern the ordinary pulled-back coefficient. Perfect direct
images of arbitrary perfect complexes under general proper-perfect
morphisms remain a further endpoint.

The degreewise local base-change algebra is also proved on the original
mate. Over a local ring, finite middle and finite flat final terms give
equivalence between residue-field surjectivity and freeness of the actual
outgoing cokernel; this implies arbitrary canonical base change. Under
that surjectivity condition, original degree-`i` cohomology is free exactly
when the original degree-`i - 1` map is surjective. The latter needs only
three finite neighboring terms and flatness of the last two, with no
boundedness or Noetherian hypothesis. The geometric projective passage over
a Noetherian local base is now proved, without reducedness: original
residue-field surjectivity gives arbitrary original base change, the
adjacent-degree surjectivity criterion detects free cohomology, and
degree-zero surjectivity already gives freeness. The public consumer passed
`1792104773395115000-70510` with only the standard three axioms.
Open-neighbourhood and arbitrary-base passages remain separate obligations.

The numerical finite-complex prerequisites are also proved on the original
objects. Finite module fibre dimensions are upper semicontinuous, and
finitely presented flat module fibre dimensions are locally constant.
Every native fibre-complex homology dimension is upper semicontinuous under
the corresponding term hypotheses, in any shape and degree. Bounded
finitely presented flat complexes have locally constant native homological
Euler characteristic on the spectrum. Public consumers cover independent
universes and report only the standard three axioms. The geometric
identification is now supplied for an actual projective embedding, and
upper semicontinuity of every original fibre-cohomology dimension is proved
for coherent relatively flat coefficients over a Noetherian base. Its public
endpoint constructs the model internally. The external all-universe consumer
passed `1792101859151326000-18032`, with only the standard three axioms.
The intrinsic alternating sum of the original fibre-cohomology dimensions
is also proved locally constant under the same geometric hypotheses. Actual
model bounds establish finite support and identify this invariant with the
native homological Euler characteristic after every residue-field extension.
The geometric leaf and public consumer passed `1792102151465195000-22103`
and `1792102216889418000-23286`; the consumer uses only the standard three
axioms. The reduced local geometric Grauert criterion is also proved:
local constancy of an original fibre-cohomology dimension gives free
original cohomology and invertibility of its original map after every ring
base change. The public endpoint constructs the model internally. Its
independent consumer passed `1792104345397963000-63013`, with only the
standard three axioms. The reduced-base result now holds over an arbitrary
Noetherian affine base, without a local-ring assumption: locally constant
original fibre dimension gives finite projective original cohomology and
arbitrary original base change. Its independent public consumer passed
`1792106107718572000-93988`, with only the standard three axioms. The local
version additionally supplies freeness. At the lower algebraic layer,
every point in the outgoing cokernel's free locus has a basic-open
neighbourhood on which the original homology mate is invertible after
every further ring map. Identification with the original residue-field
surjectivity locus, and its geometric neighbourhood endpoint, remain in
progress.

The general proper extension has started with an unconditional native
graph-closure construction. Its projection to the source is proper, is
an isomorphism over the original quasi-compact open, and is surjective
when that open is dense. The original image inclusion and projection
normalizations are explicit; the public consumer passed
`1792107508980791000-13403`, with only the standard three axioms. The
next geometric prerequisite is also proved: an affine finite-type scheme
admits an immersion into an actual standard projective chart, with the
original structural factorization and no Noetherian or field premise.
Its source passed `1792107942220884000-19839`. Chow modification and coherent support
devissage still need proof. Existing native composition of derived
pushforwards is available for the eventual Leray step.

The user-requested fetch found `origin/main` at `e3f6c75`, with cache updates
since the starting source, and the original checkout's local `main` at
`451aeda`, adding finite-etale and complex foundations. The relevant native
perfect-complex and mapping-cone dependency groups are now integrated:
thirteen existing source leaves passed one at a time, byte-for-byte from
`451aeda`, preserving their provenance and avoiding a second definition of
perfectness. The additional native tensor-right-unit leaf supplies the
actual twist tensor equivalence used by higher Serre duality. Their
native-object consumers and homology endpoints also
passed, with only the standard three axioms. These additions do not
on their own supply finite-projective replacement, perfect direct images or
proper cohomology and base change.

The clarified priority is projective geometry first: projective finiteness,
Serre duality, perfect direct image, base change, semicontinuity, Grauert and local-freeness
criteria precede the extra general-proper Chow/devissage work. The generic
finite-projective algebra and canonical maps are shared by both stages.

Verification remains leaf-local with a serialized compiler queue. No aggregate
library build, full replay or new CI claim has been made for this branch.
At this checkpoint the source-only integration route passed generated
enrollment for 753 production modules, import layout and cycle checks,
placeholder/custom-assumption checks, source policy and all 96 Python
regressions. Generated aggregate imports were refreshed without an
aggregate Lean build. Experimental files and local build artifacts are
excluded from the checkpoint.
