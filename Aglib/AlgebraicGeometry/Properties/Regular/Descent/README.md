# Conditional descent of actual regular stalks

[FlatLocal](FlatLocal.lean) defines
`Scheme.RegularityDescent.FlatLocalRegularityDescent` for the actual flat local
homomorphism between Noetherian local rings. The flat module action is induced
by that same homomorphism. The proposition is an explicit input; this file
provides no universal flat-local regularity-descent supplier.

From that input, `regular_at_image` proves regularity of the actual target stalk
under a flat scheme map. `regular_of_etale_cover` applies it to an actual etale
cover by locally Noetherian schemes with regular stalks. Stalk locality,
flatness and Noetherianity are obtained from the stated scheme hypotheses.
The regularity predicate is the existing `Scheme.RegularStalks`.

The existing etale stalk provider proves regularity ascent and remains separate
from the unsupplied descent family. Node/model constructions can consume the
conditional cover theorem without treating the family definition as a proof.
