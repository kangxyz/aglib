# Ordinary pushforward stalks and actual fibre sections

`FibreIdempotents.lean` constructs the actual canonical map
`stalkToFibreSections f y` from the ordinary stalk of `f_* O_X` at `y` to
`Γ(f.fiber y, ⊤)`. Its source is neither a completed stalk nor an etale stalk.
Its target is the literal scheme-theoretic fibre defined by the native pullback.

- `fibreSectionRestriction` restricts sections on the inverse image of an actual
  neighborhood of `y` to that fibre.
- `germ_stalkToFibreSections` proves the original germ/restriction triangle.
- `structureMap_germ_stalkToFibreSections` proves compatibility with the actual
  map of structure sheaves `f.c`.
- `structureMap_stalkToFibreSections` factors that actual stalk map followed by
  beta through the actual residue map and the literal residue-field constants
  `fibreConstants` on the same fibre.
- `exists_residue_constant_of_stalk` shows that, when `f.c` is an isomorphism,
  each element in beta's image is a residue-field constant. It makes no claim
  that beta contains every fibre idempotent in its image.

These map constructions need no properness or Noetherianity. The stronger
proper Noetherian image assertion remains a separate proof obligation: for each
idempotent `e` of actual fibre sections there must be an arbitrary element `a`
of the ordinary pushforward stalk whose image is `e`. There is no requirement
that `a` be idempotent. This module does not assume that assertion, formal
functions, flatness, Henselian hypotheses or a Stein factorization.

The ordinary functions result in `Morphisms/Proper/BirationalFunctions.lean`
remains distinct from connectedness, and from geometric connectedness of all
actual fibres. Compiler outcomes are recorded separately from this interface.
