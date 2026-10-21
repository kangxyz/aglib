# Ordered points as coordinates on the same glued line

Over a field, two actual distinct sections of the fixed projective line are normalized in their given order. The comparison uses the existing glued normalization line and its canonical projective-line isomorphism.

- `pairToLineOverIso`: the actual normalizePair followed by the canonical inverse line comparison.
- `pairToLineIso_first / pairToLineIso_second`: the original sections map to literal affine coordinates zero and one.
- `pairToLineIso_inv_first / pairToLineIso_inv_second`: inverse endpoint triangles on the same maps.

The source ranges and hashes are retained in the Lean header. The same actual
objects, structural maps and point orderings are used. No model, minimum,
regularity, or contraction existence is supplied by this extraction.
