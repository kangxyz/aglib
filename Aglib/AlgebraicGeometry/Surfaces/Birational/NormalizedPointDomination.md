# Normalized-point-chain domination

The endpoint `Scheme.NormalizedPointDomination.exists_domination` takes an
integral normal Noetherian scheme `P` of dimension at most two, Nagata data
on its actual nonempty affine charts, and an actual proper dominant morphism
`q : Q ⟶ P` with integral `Q` and invertible original function-field map.
There is no regularity hypothesis and no normality hypothesis on `Q`.

The output is an integral normal Noetherian surface `T`, actual morphisms
`beta : T ⟶ P` and `a : T ⟶ Q`, an existing literal
`Blowup.NormalizedPointBlowupChain beta`, and `a ≫ q = beta`. Both morphisms
are proper and dominant and have invertible original function-field maps.
The proof derives the dimension bound on `T`.

The original source is first normalized in its own function field; finite
normalization follows from actual adapted Nagata surface charts. On the
normal source the construction begins with `P` itself. The common models
are normalizations of the dominating schematic common-open graph component,
never the whole fibre product. Actual proper images give injections between
contracted-curve sets on different sources. A selected curve is eliminated
by strong induction on the minimum finite DVR orders of one retained
fraction; the actual normalized point exceptional generator gives strict
decrease. A second induction uses the strict finite-cardinality decrease
from the missing selected curve. At zero the actual isomorphism supplies
its inverse, and the existing literal chains and original arrows compose.
Finally the comparison is composed with the original finite normalization
map, retaining the triangle to the possibly nonnormal `Q`.

The source argument is [Stacks, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT).
The subtree splits actual chart/normalization, graph/curve-image, DVR/fraction,
and induction arguments. No supplied resolving chain, abstract path,
termination certificate or source-regular principalization is used.
