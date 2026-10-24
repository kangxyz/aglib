# Japanese domains and Nagata rings

[Defs](Defs.lean) defines `IsJapaneseRing` using finite literal integral
closures in finite extensions of the actual canonical fraction field.
`IsNagataRing` means Noetherian with Japanese actual prime quotients.
The auxiliary test universe is explicit. The interfaces below use auxiliary
universe zero; they do not assert invariance under a change of universe.

[Basic](Basic.lean), [Finite](Finite.lean) and [Localization](Localization.lean)
retain the original coefficient maps in fraction-field transport, finite
algebra ascent, quotients and localization.

[Complete local surfaces](CompleteLocalSurface.md) proves the Nagata property
for every complete Noetherian local ring of dimension at most two; neither
reducedness nor a domain hypothesis is required. The Japanese and supplied
fraction-field interfaces use a domain, including the nonnormal case.
The reduced-ring normalization interface uses its supplied total quotient
ring. These interfaces keep the actual ambient rings and scalar actions.
[Normalization](Normalization.md) also treats a
reduced Nagata ring in its supplied total quotient ring, which may lie in a
different universe.

[Completion](Completion.md) proves reducedness of the actual maximal-adic
completion of a Nagata local domain in dimensions at most one and at most
two. The dimension-two proof uses the original finite normalization, its
localizations, the associated-DVR criterion and the dimension-one result.
It supplies reducedness; normality requires its own argument.

[Polynomial](Polynomial.md) proves `IsJapaneseRing.polynomial`: the polynomial
ring over a Noetherian Japanese domain is Japanese. The coefficient ring
need not be normal, and no perfection, separability or dimension hypothesis
is imposed. Finite constant roots, a normal polynomial model and the
[normal-hull reduction](../IntegralClosure/NormalHull.md) preserve the original
fraction-field action. The Nagata definition additionally tests every actual
prime quotient.

[Rational adjunction](RationalAdjunction.md) proves finiteness of the literal
normalization of `R[x]` inside the supplied fraction field of a normal Nagata
domain `R` of dimension at most two. The local statements retain the original
maximal localization and its canonical map into that same field. The proof
uses a finite integral intermediate followed by a second localization.

[Finite-type surface algebras](FiniteTypeSurface.md) supplies three stability
interfaces. A monogenic algebra over a Nagata ring of dimension at most two
is Nagata, without a domain or target-dimension premise. For an injective,
finite-type algebraic map of domains, the target is Nagata and has dimension
at most two; that bound is proved. The essentially finite-type version uses
the actual target algebra and its localization. A complete local domain of
dimension two supplies the required base Nagata property, with no completeness
assumption on the target.

These interfaces serve the actual normal-graph and blowup-stalk constructions.
Their coefficient dimension and algebraicity conditions remain explicit;
they do not assert unrestricted finite-type stability in all dimensions.
