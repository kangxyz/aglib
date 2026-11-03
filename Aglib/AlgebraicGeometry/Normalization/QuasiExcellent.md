# Finite generic normalization from quasi-excellent affine rings

`Scheme.genericNormalization_isFinite_of_isQuasiExcellentRing` assumes an
integral scheme of topological dimension at most two and genuine
`IsQuasiExcellentRing.{u,0}` on every nonempty affine section ring. It proves
finiteness of `(W.fromSpecStalk (genericPoint W)).fromNormalization` itself.

Each affine ring has dimension at most two by the original affine-open
embedding. The ring-level N-1 theorem applies to the original coefficient ring
of relative normalization, identified as a fraction ring by
`genericSection_isFractionRing`. The native `normalizationObjIso` and
`fromNormalization_app` comparison convert this to finiteness on sections;
the existing empty-chart treatment is shared with the Nagata interface.

There is no chosen global field, trait, affine base, separatedness hypothesis,
or alternative normalization object. Quasi-compactness is not needed for this
affine-local finiteness conclusion. The auxiliary test universe is explicit.
This is not a locality theorem for quasi-excellence and does not introduce a
new scheme-level predicate. The finite-normalization theorem alone does not prove resolution existence.
The separate completed-stalk result is described below.

## Actual completed normalization stalks

`genericNormalization_completion_normalDomain_of_dim_eq_two` proves both
domainhood and integral closedness of the literal completed stalk at an
original dimension-two normalization point. It chooses an actual affine
base open and its actual affine preimage; finite normalization supplies the
original finite section-ring algebra. The normal actual stalk is identified
with that affine ring's original prime localization. The finite G-ring
completion theorem and the literal completion ring equivalence give the
conclusion. No resolution, global base, or replacement normalization is used.

The finite singular-support assembly and the deduction that singular stalks
have dimension two belong downstream to surface criterion theory.
