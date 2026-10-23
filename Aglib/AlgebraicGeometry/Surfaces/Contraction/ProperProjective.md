# Projective presentations along the original point-blowup chain

`Surfaces.Contraction.exists_projective_embedding_of_pointBlowupChain` descends
an actual finite projective embedding through the supplied original finite chain.
Its target remains the original integral regular Noetherian scheme, and the
embedding retains its prescribed map to the same Noetherian affine base.

Every reverse step uses `exists_projective_embedding_of_pointBlowup` for the
actual original closed point and its two-dimensional local ring. Local
Noetherianity and compactness give Noetherianity of each intervening source.
The given chain supplies its regularity and integrality. No replacement target
or abstract projectivity supplier is introduced.

This is the reverse induction in the proper-surface projectivity argument.
The forward construction of a projective presentation of the top stage,
followed by its Chow comparison graph, remains a separate input. The general
proper-surface projectivity theorem is not yet supplied by this candidate.

`exists_projective_embedding_of_projective_pullback` supplies the intervening
closed comparison graph into the literal pullback of a separated modification.
It composes an actual closed embedding of that pullback with the original graph,
then invokes the reverse induction. Its remaining input is the concrete forward
embedding, not projectivity of the original target.

`exists_cartier_contraction_of_projective_embedding` additionally turns an actual
finite closed embedding into the published projective contraction input. It
derives the strictly positive exceptional twist and finite coordinate reindexing,
rather than asking the caller to choose them. The output retains the prescribed
affine-base map, original full field point, pulled Cartier ideal, canonical
blowup lift and literal complement comparison. General properness alone still
does not invoke this adapter until the forward construction supplies its embedding.
