# Original small-etale cohomology over fields

This family retains original `Sheaf.H`, standard coefficient value universe
`u+1`, and arbitrary independent Ext universes.

## Field covers and original cochains

[FiniteGaloisCover](FiniteGaloisCover.lean) refines actual terminal covering
sieves over an arbitrary field by finite Galois field covers.
[CoverEffacement](CoverEffacement.lean) kills each individual positive
original cohomology class by such a cover, with the normalized
constant-integer/free-terminal source map.
[PullbackEffacement](PullbackEffacement.lean) applies the general
[original source-square zero theorem](../SlicePullback/SourceSquare.lean)
to obtain vanishing under the original geometric pullback of that same class.

[OverlapH1](OverlapH1.lean) and [ArtinianOverlap](ArtinianOverlap.lean)
identify original represented Ext1 with original chart cohomology and use
native semilocal Picard triviality. [GaloisCechCover](GaloisCechCover.lean)
and [GaloisOverlapH1](GaloisOverlapH1.lean) retain the actual covering family,
Artinian overlap and first free-resolution term.
The complete comparison is supplied by
[the represented Gm interface](../Kummer/EtaleSliceMultiplicative.lean);
only the ambient Ext universe is public in these vanishing results. Slice and
chart Ext sizes are chosen internally. The actual free tuple comparison uses
[the general unique-family constructor](../../../CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/UniqueFamily.lean).

[AmitsurComplex](AmitsurComplex.lean), [GaloisCech](GaloisCech.lean) and
[GaloisPrimitives](GaloisPrimitives.lean) transport actual multiplicative
Amitsur primitives through the original differentials and sheafification
adjunction.

## Degree two and higher finite coefficients

[GmH2](GmH2.lean) proves original `H2(gm(Spec E))` vanishing when
`E` is algebraic over `K(t)` and `K` is algebraically closed.
[RootsH2](RootsH2.lean) uses the original Kummer sequence for positive
invertible roots. [ConstantH2](ConstantH2.lean) retains the actual
constant-root coordinate.

[SeparablyClosedRootsH2](SeparablyClosedRootsH2.lean) and
[SeparablyClosedConstantH2](SeparablyClosedConstantH2.lean) extend the root
and cyclic conclusions to algebraic extensions of `k(t)` with separably
closed, possibly imperfect `k`. The construction uses actual
[perfect-function-field algebra](../../../FieldTheory/PurelyInseparable/README.md)
and original purely inseparable root pullback. It does not assert Gm
invariance or Gm H2 vanishing over arbitrary imperfect separably closed
constants.

[FiniteTrivialization](FiniteTrivialization.lean) produces an actual finite
Galois trivializing cover for every genuine FLC coefficient.
[FiniteMonodromy](FiniteMonodromy.lean), [SylowMonodromy](SylowMonodromy.lean),
[SylowLine](SylowLine.lean) and [FiniteCyclicLine](FiniteCyclicLine.lean)
retain the original finite fibre action and construct the finite
prime-to-p field and cyclic coefficient monomorphisms.
[FiniteH2](FiniteH2.lean) then gives original H2 vanishing by induction on
the actual fibre cardinality, with the original cokernel and finite-field
restriction/trace maps.

[FiniteCohomologicalDimension](FiniteCohomologicalDimension.lean) proves
`finite_cohomology_subsingleton_of_separablyClosed_ratFunc`:
if `k` is separably closed, `E/k(t)` is algebraic, `p` is prime and
invertible in `Γ(Spec k, ⊤)`, and `F` is genuine FLC with
`KilledBy p F`, then original `Sheaf.H F q` is a subsingleton for
every `q ≥ 2`.

[RootsVanishing](RootsVanishing.lean) proves the corresponding all-degree
cyclic and root statements for every positive `n` invertible in
`Γ(Spec k, ⊤)`. The actual cyclic short exact sequences and
constant-root comparison are retained. Arbitrary algebraic degree and
imperfect separably closed constants are allowed. These finite-coefficient
results do not assert higher Gm vanishing.

[Purely inseparable comparison](PurelyInseparable/README.md) uses the
original finite-etale base-change functor for arbitrary, including infinite,
purely inseparable extensions. Its original root-cohomology pullback
is bijective in every degree for positive invertible order, with independent
source and target Ext universes.

[Finite direct-image local products](FiniteDirectImageExact/LocalProduct.lean)
package the original splitting-chart component inclusions as one coefficient-free
site natural transformation. Continuous pushforward gives the original
restriction maps on sections; the existing fan and section bijection retain the
local product comparison for arbitrary original abelian coefficients.

[Finite-etale transfers](FiniteEtaleTransfer/Trace.lean) supply the original splitting charts, matching equations and actual finite-flat rank to the generic finite-sum construction. The normalized source remains the original constant integer sheaf; the finite separable field specialization uses the actual field degree.

[Local finite comparison](SeparableExtension/FiniteConstants/LocalFiniteComparison.lean)
transfers bijectivity of original cohomology pullback across the actual finite
direct-image square, retaining four independent Ext worlds. Its projective-line
corollaries keep the Noetherian strictly henselian local base, the original
killed coefficient or finite constant coefficient, and every cohomological
degree.

[HenselianFieldComparison](SeparableExtension/FiniteConstants/HenselianFieldComparison.lean) applies the general pullback comparison maps to the original coefficient changes. For schemes finite over the original projective line, the finite constant-coefficient restriction theorem retains a Noetherian henselian coefficient algebra whose actual residue field is separably closed and finite purely inseparable over the ground field.

[Native line comparison](SeparableExtension/FiniteConstants/NativeLineComparison.lean)
retains the original cohomology pullback along the actual map `P1_K → P1_k`.
The canonical line base-change isomorphism and original inverse-image
composition identify it with the categorical field comparison. Both fields are
separably closed; the original coefficient is killed by a nonzero integer, and
the conclusion holds in every degree.
