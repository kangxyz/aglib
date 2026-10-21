# Minimal finite free covers and resolutions

The source uses native `ModuleCat` objects, linear maps, and
`CategoryTheory.ProjectiveResolution`.

`ModuleCat.exists_minimal_finite_free_cover` applies to a finite module over a
commutative local ring. It supplies a finite free module and a surjective map
whose kernel lies in the maximal ideal times the source. No Noetherian
hypothesis is needed for this cover. The proof lifts a basis after tensoring
with the residue field. Nakayama gives surjectivity, and equality of dimensions
over the residue field gives injectivity after base change. The kernel formula
for tensoring with a quotient then proves the stated containment.

`ModuleCat.exists_minimal_finite_free_resolution` applies when the ring is also
Noetherian and the module has projective dimension at most a specified natural
number `n`. It supplies an actual projective resolution with finite free terms,
zero terms in degrees greater than `n`, and every differential taking values
in the maximal ideal times its target. Exactness is part of the constructed
resolution, rather than an additional input.

The resolution proof is induction on the given bound. At bound zero, the
module is projective and hence finite free, giving the resolution concentrated
in degree zero. At a successor bound, the minimal cover has a finite kernel
whose projective-dimension bound is one smaller. The recursively constructed
kernel resolution is augmented by the cover's free source. The cover's kernel
containment supplies minimality of the newly inserted differential; later
differentials retain the inductive containment.

The cover is consumed by the dimension bound in
`Aglib.RingTheory.LocalRing.ResidueProjectiveDimensionBound`. The full resolution
is consumed by the Koszul comparison in
`Aglib.RingTheory.RegularLocalRing.ResidueProjectiveDimension`. Neither
construction assumes regular locality, a regular sequence, or a converse
regularity criterion.

These are native new proofs against Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, authored in the Aglib checkout at
`3a4d549981ced306d89d3ed55418c9e6a25f86c4`. The implementation constructs
minimal covers directly and does not depend on a separate cancellation
algorithm for arbitrary complexes.
