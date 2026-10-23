# Faithfully flat augmented Amitsur exactness

This family constructs the actual Amitsur complex of an arbitrary module and
proves exactness under faithfully flat scalar extension. Import
`Aglib.Algebra.Homology.Amitsur` for the completed interface.

For `R S : Type u`, commutative ring structures, `Algebra R S`,
`Module.FaithfullyFlat R S` and `M : ModuleCat.{max u v} R`, the endpoints in
`ModuleCat.Amitsur` are:

- `augmentedComplex_exactAt R S M n`: exactness at every augmented degree `n`;
- `augmentedComplex_acyclic R S M`: acyclicity of that original augmented complex;
- `isZero_homology_augmentedComplex R S M n`: zero homology at every augmented degree;
- `complex_exactAt_succ R S M n` and `isZero_homology_complex_succ R S M n`:
  exactness and zero homology at every positive unaugmented degree `n + 1`.

The ring universes are aligned at the native `CommAlgCat` conerve interface.
The coefficient module category has universe `max u v`, with `v` independent.
`Reflection.lean` separately allows independent base-ring, scalar-algebra and
module universes. No coefficient-module flatness, finiteness, Noetherian,
field or separability hypothesis occurs.

`Conerve.lean` uses `Arrow.cechConerve` of the original algebra unit. Its terms
are the actual native finite wide pushouts, with original factor maps `ι`.
`zeroIso` identifies the first term with `S`, and `successorTensorIso` splits
off its original first `S` factor. `Modules.lean` tensors those original maps
with `M`. It applies the native alternating coface complex and native
`CochainComplex.augment`; the augmentation remains the original `m ↦ 1 ⊗ m`.

`Coordinates.lean` gives actual equations under the canonical tensor
comparisons: the zero coface inserts the leading unit, each successor coface
is the preceding insertion tensored with `S`, and the original degree-zero
second coface inserts the trailing unit. The original differential is the
alternating sum in that order. These equations identify the native complex
with the usual successive tensor formula without defining a second complex.

After adding one original leading `S` factor, `ScalarExtension.lean` constructs
a native extra degeneracy. Its retraction and contractions use the original
multiplication of the leading factors. `Split.lean` proves a generic native
null homotopy of the resulting augmented complex. `Comparison.lean` uses the
canonical tensor associator, with the identity in augmentation degree, to
compare it with scalar extension of the original complex. `Reflection.lean`
then applies native faithfully flat tensor exactness reflection in each degree.

This is the algebraic Amitsur supplier. Applications to actual etale or Zariski
coefficient sheaves and their derived comparison belong to their geometric
owners.
