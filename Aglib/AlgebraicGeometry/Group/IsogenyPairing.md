# Actual point pairing for curve isogenies

`IsogenyPairing.lean` constructs the positive frame-transport pairing on the
rational points of the actual categorical kernels. The construction uses the
original line bundles, group laws, translation morphisms and structural map
from the ground field to global functions.

## Inputs and conventions

Let `k` be algebraically closed and let `f : E ⟶ D` be a finite, etale,
surjective morphism of group schemes. Both original schemes have native
`Curve.Properties`; their native coherent genera are explicitly one. The
smooth relative dimension-one and separated instances are the corresponding
curve hypotheses. Let `n : ℕ`, let `HasGeometricDegree f.hom.hom n` hold, and
let `d : D ⟶ E` satisfy the source triangle
`f.hom.hom ≫ d.hom.hom = (𝟙 E.X) ^ n`.

The Picard class of a reverse-kernel point is the positive point-minus-origin
class. `DualIsogeny.reverse_pointClass` identifies its pullback by the actual
`f` with the point class after `d`; consequently that pullback is trivial.
A chosen actual O-linear frame is compared with its pullback by a kernel
translation. Positive transport is the unit carrying the original frame to
that translated frame. The proper-curve constants equivalence converts this
unit to `kˣ`. The source multiplication triangle proves that its `n`th power
is one.

## Main interfaces

- `evaluationCharacter` is the resulting homomorphism
  `KernelPoints f →* rootsOfUnity n k` for each `y : KernelPoints d`.
- `evaluationHom` proves multiplicativity in `y`, using actual tensor frames
  and the native point-class addition theorem.
- `kernelPairing` expresses the same construction as
  `Additive (KernelPoints d) →+
  (Additive (KernelPoints f) →+ Additive (rootsOfUnity n k))`.
- `kernelPairing_injective` proves injectivity with the preceding hypotheses;
  it requires no invertibility assumption on `n` in `k`.
- `kernelPairing_bijective` additionally assumes `IsUnit (n : k)` and proves
  perfectness of this actual additive map.

`KernelPoints f` means morphisms from the actual terminal `k`-scheme to
`Kernel.group f`, rather than a chosen abstract group of the same cardinality.
Frame choice and line-bundle representative independence are proved by
`frameKernelCharacter_independent` and `lineBundleKernelCharacter_iso`.

## Proof of perfectness

The existing kernel torsor identifies the literal scheme kernel pair with
`ker(f) × E`. Over the algebraically closed field, the rational kernel
translation graphs jointly cover that kernel pair. `deckInvariant_descends`
uses this cover and the native etale sheaf axiom to descend an invariant
section. Applied to the actual frame sheaf, a trivial character therefore
forces the original line-bundle class to vanish. Native Abel injectivity then
forces the reverse-kernel point to be the identity.

For surjectivity, `reverseKernelPoints_card` decomposes the actual fibre of
`[n]` into the actual fibres of `f` and uses the proved multiplication degree
`n * n`. `kernelRootCharacters_card` uses the actual exponent bound and enough
roots of unity, then native finite-abelian character duality. These cardinality
arguments complete the already proved injective map. No reverse-kernel
cardinality or dual degree is an input.

## Semilinear comparison and arithmetic specialization

`FramePullback.transportUnit_naturality` proves that positive transport follows
actual scheme pullback of global units. `pointDivisorClass_eq_ideal` identifies
the normalized class with the positive point ideal difference, and
`pointDivisorClass_semilinear` follows the literal point and origin squares.
`evaluationCharacter_semilinear` combines these facts with a commuting
isogeny square and actual translation conjugacy.

The focused [Galois specialization](IsogenyPairing/Galois.md) constructs the
pairing on original geometric kernel points over an arbitrary ground field,
proves its native absolute-Galois equation, and supplies the field fundamental
group adapter in characteristic zero. Its perfectness retains invertibility of the actual degree
in the ground field. Weil alternation is a separate mathematical obligation.
