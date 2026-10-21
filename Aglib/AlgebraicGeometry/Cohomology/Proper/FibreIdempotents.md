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

These map constructions need no properness or Noetherianity. The focused
[Stalk](FibreFormalFunctions/Stalk.lean) leaf proves
`ProperFibreFormalFunctions.exists_stalk_restrict_eq_of_isIdempotentElem`:
for proper `f : X ⟶ Y` with locally Noetherian `Y`, every idempotent of
`Γ(f.fiber y, ⊤)` has a preimage under this same ordinary stalk map.
The preimage is arbitrary and need not be idempotent. Its local-section
equivalence and germ law identify the original map with actual local-fibre
restriction. The [affine theorem](FibreFormalFunctions.lean) supplies the
image witness over the local spectrum using formal functions. No flatness,
Henselianity, completeness, Stein factorization or object effectivity is assumed.

[ConnectedFibres](../../Morphisms/Proper/ConnectedFibres.md) proves geometric
connectedness for proper surjective `f` over a locally Noetherian target with
`IsIso f.c`. Its direct affine proof uses the arbitrary-ideal image theorem
and actual flat base change; it does not depend on the ordinary-stalk image
specialization. The lower
[birational functions theorem](../../Morphisms/Proper/BirationalFunctions.md)
requires no Noetherianity, while its geometric-connectedness specialization
retains local Noetherianity of the target.
