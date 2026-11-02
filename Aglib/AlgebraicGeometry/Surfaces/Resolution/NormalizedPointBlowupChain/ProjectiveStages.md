# Projective embeddings of the actual interior stages

Source: [ProjectiveStages.lean](ProjectiveStages.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.ProjectiveStages`.
The namespace is `AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain`.

`exists_interior_projective_embeddings` uses a commutative DOMAIN R, an
integral locally Noetherian original X, an actual proper normalized-point
chain c, and one finite-coordinate closed embedding of X over R with its
actual dominant structural map and finite generic-image field extension.
It chooses ONE finite-coordinate embedding for each strict interior native
cut, on exactly c.stage i. It retains c.toBase i, its structural triangle,
the original generic-image field-map composition and derived finiteness.
Properness of each prefix follows from the actual total proper chain.
ProjectiveEmbedding constructs the actual embedding; no base finiteness or global Nagata is added.

The choice family is a dependent finite tuple on the existing strict interior
indices. It is not a new chain, scheme, field or compatibility model.
Both original endpoint embeddings stay outside this choice family. Thus the
caller retains jX and jZ exactly, with native endpoint eqToHom transport;
there is no forced equality between their coordinates or canonical objects.

`isIso_of_length_eq_zero` proves invertibility of the ORIGINAL map of a
zero-length normalized chain. It has no scheme-geometry or embedding premise.
The later canonical consumer must still use its two original embeddings
and their actual trace/counit comparison in that case. No such canonical
comparison or surjectivity theorem is asserted here.

No normality, regularity, dimension, rationality, canonical coefficient,
generation, Gorensteinness or frame is an input or output. This is only the
actual geometric D1 preparation for the reviewed singular-trajectory plan.
