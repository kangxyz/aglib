# Actual quadratic alternatives from original exceptional cohomology

API: [exceptional_original_quadratic_alternatives](QuadraticClassification.lean#L46).

## Scope and precise imports

The thin consumer is
`Surfaces/Resolution/RationalDoublePoint/QuadraticClassification`.
Import `ExceptionalHilbert/Projective` and the unique lower
`QuadraticClassification/Core`. The lower imports the actual coordinate/cubic
and quadratic algebra suppliers precisely.
No new cone, generators backend, polynomial coordinate change, Hilbert proof,
or classification proof is introduced.

## Exact hypotheses

Retain `A : Type u`, `[CommRing A]`, `[IsLocalRing A]`, `[IsDomain A]`,
`[IsNoetherianRing A]`, `[IsIntegrallyClosed A]`, `hd : ringKrullDim A = 2`,
`hA : IsNagataRing.{u,0} A`, actual universal normal-modification rationality,
and `hsing : ¬ IsRegularLocalRing A`.

The remaining genuine geometric inputs are exactly the existing Projective
consumer's original inverse-exceptional-line H0 subsingleton and H1 finrank one.
Their sheaf is the dual of the actual exceptional line on the full original
exceptional scheme, and their structural map and residue field are unchanged.
The canonical identification eW is not silently assumed constructed.

## Exact output

Return the following disjunction, with all polynomials over the original
`ResidueField A`.

### Case I

Produce actual `t : maximalIdeal A`, `g : Fin 2 → maximalIdeal A`, and
`q : MvPolynomial (Fin 3) (ResidueField A)` with:

- the original `CaseOne.orderedGenerators t g` span the actual maximal ideal;
- `q ≠ 0` and `q.IsHomogeneous 2`;
- the entire original `RingHom.ker (CaseOne.canonicalConeMap t g) = span {q}`;
- the original t is nonzero, actual `dehom q` is nonzero and has total degree ≤2;
- `Nonempty (CaseOne.Presentation A t g (dehom q))`;
- global homogeneous nonsquare information:
  `¬ ∃ c : ResidueField A, c ≠ 0 ∧ ∃ L,
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q = C c * L^2`;
- the exact existing Case-I affine predicate for that original dehom chart.

The global negative information is retained rather than discarded after
choosing the first chart. Thus later permutation consumers can use the same
actual polynomial/permutation laws to obtain the negative predicate on every
original chart; this wrapper does not assert an unproved all-chart theorem.

### Case II

Produce actual original `t s z : maximalIdeal A`, original generation
`maximalIdeal A = span {t,s,z}`, and the entire original normalized kernel on
`![s,z,t]` equal to `span {(X 1)^2}`. Produce one true original
`F : CubicRelation t s z` with zero remainder and nonzero original residue
binary cubic. This is the existing coordinate/cubic output, not a marker or
stable special-cubic assertion.

## Proof composition

Use the original-generator producer and genuine complete Hilbert function,
then call the thin Hilbert sibling in `QuadraticClassification/Core`. That
lower obtains the entire original kernel once and invokes its unique split
at the actual full-quadratic-kernel boundary. The old theorem retains its
exact public telescope and original output; no duplicate split survives here.
The same lower handles an initial given full cone without adding a Hilbert
premise to an original path theorem.

## Boundaries

No assertion of Gorenstein preservation, canonical eW, a child canonical
identification, actual marked entry, a stable marker, or finite termination
is part of this result. Native marker transport is handled separately and is not an input to this
classification theorem.
