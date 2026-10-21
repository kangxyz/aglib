# Regularity from finite projective dimension of the residue field

`IsRegularLocalRing.of_residueField_hasProjectiveDimensionLE R n` proves the
residue-field regularity criterion for a commutative Noetherian local ring.
Its homological premise is the native instance
`CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R (IsLocalRing.ResidueField R)) n`,
where `n` is any natural number. The conclusion is Mathlib's actual equality
between the maximal ideal's minimum number of generators and the Krull
dimension. There is no regular-sequence or converse-criterion hypothesis.
This is the input needed by flat-local regularity descent: the native finite
bound supplied by `FlatDescent.lean` has precisely the required type.

## Cotangent dimension and projective dimension

`IsLocalRing.finrank_cotangentSpace_le_residueField_projectiveDimension` proves
the lower bound for every commutative Noetherian local ring, including rings
whose residue field has infinite projective dimension.

Given a bound `n`, lift a cotangent basis and compare its native Koszul complex
with the finite minimal free resolution from
`ModuleCat.exists_minimal_finite_free_resolution`. The comparison lifts the
residue augmentation, using projective source terms and an exact target.

The comparison reflects maximal-ideal membership by degree induction. Degree
zero follows from the augmentation. At the next degree, residue injectivity
of the previous comparison supplies an actual linear left inverse over the
original ring. Minimality sends maximal-ideal multiples into its square.
The chain-map identity and left inverse put the Koszul boundary in that square;
`ChainComplex.Koszul.mem_maximalIdeal_smul_top_of_d_mem_sq` then puts its input
in the maximal ideal times its term.

If the cotangent dimension exceeded `n`, the comparison's top target would
vanish. The top Koszul term is the ring, so reflection would put `1` in its
maximal ideal. Thus the cotangent dimension is at most every finite bound.
The `HasProjectiveDimensionLT` characterization yields the unconditional
inequality; the nonzero residue field excludes projective dimension bottom.

## The regularity criterion

The independent native theorem
`ModuleCat.residueField_projectiveDimension_le_ringKrullDim` supplies the
complementary upper bound when the residue field has finite projective
dimension. Its proof uses quotient projective-dimension bounds, regular-element
dimension induction, and the depth-zero socle argument. Combining the two
bounds makes the cotangent dimension at most the Krull dimension. Mathlib's
generator bound gives equality and hence `IsRegularLocalRing R`.

The module retains explicit small cases. A projective residue field is finite
free and faithful, while its annihilator is the maximal ideal; hence the ring
is a field, without a Noetherian hypothesis. For projective dimension at most
one, the maximal ideal is projective and finite free. Commutativity forces a
nonzero free ideal to have one basis vector, which is a nonzerodivisor. The
generator bound and regular-element dimension formula prove regularity.

## Sources and implementation basis

The exact classical statement is
[Stacks, Proposition 10.110.5 (00OC), (1) implies (3)](https://stacks.math.columbia.edu/tag/00OC).
The two inequalities correspond to
[Lemma 10.110.3 (00OA)](https://stacks.math.columbia.edu/tag/00OA) and
[Lemma 10.110.4 (00OB)](https://stacks.math.columbia.edu/tag/00OB).
Their statements and displayed proof routes were inspected on 2026-10-21.
The current corrected comparison lemma
[10.71.4 (00LS)](https://stacks.math.columbia.edu/tag/00LS) allows a free source
complex and an exact target resolution, exactly as required here. The native
proofs construct their objects and maps rather than importing those statements
as assumptions.

The work was authored in the original Aglib checkout at
`3a4d549981ced306d89d3ed55418c9e6a25f86c4`, against Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The accepted native comparison basis
was `aglib-next-release@53026ed980426d54f2b35b3310e27e2d2cb14293`; the minimal
resolution, Koszul linear-part, and residue projective-dimension providers are
new native foundations developed from that basis.
