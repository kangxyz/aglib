# A Cartier first-order neighborhood test

`CartierNeighborhood.lean` concerns the original proper dominant birational
q:W→B between integral schemes, with B locally Noetherian and its actual
stalks normal. Birationality is the actual native functionFieldMap-isIso
hypothesis, together with the given dominance instance. Local Noetherianity
of W is derived from properness of q; no global compactness is imposed.

The original i:E→W and j:D→B carry native explicit Hom.IsEffectiveCartier
proofs. The given e:E≅D and its original square are retained. The sole
first-order premise is IsIso of the original canonical idealPullbackMap
after pullback by i. A slightly stronger theorem needs only Epi of that
same pulled map. Both produce an actual target open V containing range j,
with the original q restricted to V an isomorphism.

The proof does not assume equality of the pulled ideal, flatness of q,
étaleness, or an ambient regular model. It first takes the ordinary actual
stalk support of the cokernel of the original ideal comparison. The actual
line-module hypotheses make this cokernel finite-type quasicoherent and
its support closed. On range i, the original closed-pullback stalk
comparison and local Nakayama give epimorphy of the original stalk map.
Its cokernel therefore vanishes there. The complement of its support is
an actual source open containing all of E, and the original restricted
comparison is epi there. This does not infer sectionwise surjectivity
from sheaf epimorphy.

The proved native Detection theorem compares the actual inclusion maps
and identifies the original inverse-image ideal with the original ideal
of E on this source open. This avoids any flat pullback of kernels or
applying CartierAvoidance to a square before it is proved cartesian.
The given e implies that the resulting open part of every point fibre
over D consists of its original E point. The native quasi-finite-at
criterion makes this singleton clopen in the whole fibre. Proper
birational morphisms onto the actual normal locally Noetherian B have
geometrically connected fibres, so this singleton is the entire fibre.
The existing proper birational finite-fibre theorem supplies an actual
target isomorphism open at each point of D; target locality glues their
union. Empty divisors and empty selected opens are included.

The public endpoints are
`Scheme.exists_isIso_restrict_of_isProper_birational_of_cartier_pullback_epi`
and its `..._isIso` corollary. No field, base, splitness, excellence,
resolution, surface factorization, or minus-one contraction conclusion
is part of this general neighborhood lemma. Native compiler evidence and
independent mathematical review are tracked separately in the assigned
investigation directory.
