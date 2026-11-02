# Exact regular-parameter neighbourhood of a prime

All declarations are in `IsRegularLocalRing` and retain the actual canonical
prime and Away localization maps.

`exists_regular_generators_atPrime` lifts an original regular system of `d`
parameters from `Localization.AtPrime p`. It preserves its length, weak
regularity after the original localization, and exact localized prime ideal.
This step needs a commutative ring, a prime `p`, regularity of that prime
localization, and its dimension equality. The original ring need not be
Noetherian at this lifting stage.

`exists_regular_sequence_away` additionally assumes the original ring is
Noetherian. It constructs a list `rs : List R` of length `d` and `f ∉ p` such
that the same numerator list maps to a weakly regular sequence in the actual
`Localization.Away f`, with generated ideal exactly
`p.map (algebraMap R (Localization.Away f))`.

The construction chooses the numerators first. A common bound `g` clears
their prefix colons; an existing finite-ideal denominator `c` clears the
reverse inclusion of the original prime into their ideal. On the single
final ring `Away (g*c)`, the same bounds prove regularity and exact ideal
equality. No iterated localization structure is selected. Neither equality of
supports nor regularity only at nearby primes replaces either conclusion.

`exists_regularPair_away` specializes the same length-retaining construction
to dimension two. It returns actual `a,b : Localization.Away f` with
`span {a,b}` equal to the extended original prime, `a` regular in the Away
ring, and `b` regular modulo the actual principal ideal `span {a}`. This is
only list length two and the native quotient comparison, not another
regular-parameter proof. Properness follows from `f ∉ p`; for a later domain
chart the existing proper-pair swapping law gives the opposite orientation.

No localness, domain, field, excellence, J2, or finite-type hypothesis on the
original ring is added. The old `Blowup/RegularPair` local theorem and the
single-scalar `Regular/Localization` remain unchanged. The original J2
consumer discards only the additional length conclusion of the shared lift.

## Status and geometric boundary

The complete upper owner `f58f1114` passed the normal native check `own180`
(2.8 seconds for the leaf, 5.0963 seconds total, 2412 jobs, exit zero and no
aggregate guard). The initial source `5ce43e73` had failed `own179` at the
unknown `sup_bot` name; the accepted repair uses the existing native
`sup_bot_eq` theorem at that single site.

The shared generic `Regular.SequenceLocalization` owner `11fe9dd7` passed
its complete normal check `own177` (3.9 seconds for the leaf, 6.008 seconds
total). The name-qualified J2 consumer `cba7ed5b` separately passed its complete
normal check `own183` (18 seconds for the leaf, 22.6590 seconds total, exit zero
and no aggregate guard), after the ordinary name ambiguity in `own182`.

The future scheme consumer must still identify the original closed-point
kernel ideal on its actual affine chart and retain the native basic-open
restriction algebra. This algebraic theorem does not establish that adapter,
global one-pole gluing, a trace comparison, or a uniform scalar bound.
