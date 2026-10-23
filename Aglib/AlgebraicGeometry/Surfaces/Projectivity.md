# Projectivity of regular proper surfaces over an affine base

`Scheme.Surfaces.exists_projective_embedding_of_isProper` constructs a finite
closed projective embedding of the original integral regular Noetherian scheme
of dimension at most two over any Noetherian affine base. Its structural map
is exactly the supplied proper morphism. Projectivity and an ample bundle are
conclusions of the construction rather than hypotheses.

The proof uses an actual projective Chow modification and the original generic
inverse to obtain a finite regular point-blowup chain dominating it. The full
tensor-Rees construction embeds the literal pullback of that chain over the
projective modification. A closed comparison graph then embeds the chain's
top stage. Reverse contraction of each original point blowup transfers the
embedding back to the unchanged original target with its exact base triangle.
No flatness of the modification, regularity of its source, residue-field
identification, excellence, trait or chosen field is required.

`exists_standard_projective_embedding_of_isProper` reindexes to actual
`ULift (Fin (n + 1))` coordinates. Nonempty coordinates follow from the original
integral source and its actual map to projective space.

This is the proper-projectivity assembly used by
[proper contraction](Contraction/Proper.md) on the actual inverse image of
an affine base neighbourhood. Its supplied proper morphism remains the
structural map in the resulting projective embedding.
