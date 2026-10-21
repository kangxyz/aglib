# Proper birational surface isomorphism locus

`exists_isIso_restrict_finite_closed_complement_of_isProper_birational`
constructs an actual target open `U` such that the literal restriction `f ∣_ U`
is an isomorphism and the complement is a finite set of closed points.

The premises are integral source and target, a Noetherian target with
`NormalStalks`, topological Krull dimension at most two, properness, dominance,
and invertibility of the original `functionFieldMap f`. The source need not be
regular. No excellence, projectivity, Henselianity, perfect-field, model-existence
or supplied isomorphism-locus family is assumed.

`Hom.targetIsomorphismLocus` is the union of all actual opens on which the original
morphism restricts to an isomorphism. The restriction to this union is an
isomorphism by target locality and the native double-restriction comparison.
Every such open is contained in it.

A nonclosed point has a strict specialization. The native stalk/coheight
identity and strict-specialization dimension inequality show that its stalk has
dimension at most one. A normal Noetherian local domain of dimension at most one
is a valuation ring, including the field case. The separate coheight-at-most-one
theorem applies to all such points, including a closed generic point in dimension
zero, and requires no global dimension bound. The existing proper birational
valuation-ring extension theorem then supplies an actual isomorphism restriction
around that point with the same original function-field map.

The complement of the union is closed and all its points are closed. Its
finiteness uses both Noetherianity and scheme sobriety: decompose it into finitely
many irreducible closed subsets, take each actual generic point, and use the
closedness of that point to identify the component with its singleton.
Noetherianity and the T1 axiom alone would not justify this conclusion.

The primary geometric locators are [Stacks Tag 0BFP, Lemma 33.17.3](https://stacks.math.columbia.edu/tag/0BFP)
and the first step of [Stacks Tag 0C5R, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
The Lean proof uses the actual native providers described above; the citations
do not replace its proof obligations. This module proves only the isomorphism-locus
step and makes no point-blowup factorization, contraction or minimal-model claim.
