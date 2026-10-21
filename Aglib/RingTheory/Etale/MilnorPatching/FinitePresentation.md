# Universal etale Milnor patching

`Aglib.RingTheory.Etale.MilnorPatching.FinitePresentation` supplies
`RingHom.Etale.MilnorPatching.etalePatching`, whose type is the existing
`RingHom.Etale.MilnorPatching.EtalePatching` proposition.

The pointwise theorem `etale_fiberMap` uses the original six commutative
rings in one universe and the original seven homomorphisms and two
commutative squares. It assumes that \(f:R\to T\) is surjective, that
\(r:R\to C\) and \(s:S\to D\) are etale, and that the specified
\(T\)-algebra equivalences

\[
T\otimes_R C\simeq U,\qquad T\otimes_S D\simeq U
\]

send \(1\otimes c\) and \(1\otimes d\) to the original maps into \(U\).
Its conclusion is etaleness of the original `fiberMap` between the literal
fiber rings. There is no finite-module, Noetherian, flatness-of-\(g\),
faithfulness, input-patching, or output-finite-presentation premise.

## Finite generation and the actual relation ideal

`surjective_of_tensor_components` applies the existing joint tensor
conservativity theorem to the actual cokernel of a linear map. The
canonical cancellation

\[
(R\otimes_P A)\otimes_A N\simeq R\otimes_P N,
\qquad (r\otimes a)\otimes n\longmapsto r\otimes an
\]

extends this result to every algebra \(A\) over the original base
\(P=R\times_T S\). The corresponding finite-generation theorem chooses
finitely many original elements occurring in the component tensor
generators. It applies equally to modules over a polynomial algebra over
\(P\), without requiring that algebra extension to be flat.

Algebra finite type descends by the same finite selection applied to
algebra generators. The image of the resulting finitely generated
subalgebra becomes surjective on both components, so its module cokernel
vanishes by joint tensor conservativity.

`finitePresentation_of_flat_of_component_baseChanges` now chooses an actual
surjection \(A=P[x_1,\ldots,x_n]\to Q\) and its original kernel \(K\).
Flatness of \(Q/P\) gives the canonical equivalences
between \((R\otimes_P A)\otimes_A K\) and the actual kernel after
\(R\)-base change, and likewise for \(S\). This is the native
`Algebra.kerTensorProductMapIdToAlgHomEquiv`, which retains the actual
kernel inclusion and uses quotient flatness. Each component kernel is
finitely generated because its map is a surjection between finitely
presented component algebras. Module finite-generation descent over \(A\)
therefore makes \(K\) finitely generated. The original polynomial
presentation then proves \(Q/P\) finitely presented.

The etale endpoint obtains flatness from [Flat](Flat.lean), formal
unramifiedness and the canonical component equivalences from
[General](General.lean), and finite presentation from this argument.
The `Flat` and `FinitePresentation` leaves discharge the output properties
used by the lower formal-unramifiedness combination theorem. The universal
endpoint therefore retains only the original component hypotheses.

## Source correspondence and boundary

The primary target is [Stacks 08KQ(5)](https://stacks.math.columbia.edu/tag/08KQ)
in [Situation 08KH](https://stacks.math.columbia.edu/tag/08KH), inspected on
2026-10-21. Its quotient boundary is identified with the supplied tensor
boundary by the existing `quotientBoundaryEquiv` and its equation on
quotient classes. Tensor commutation and coordinate swapping preserve the
original maps. The source finite-presentation route is
[Stacks 08KP](https://stacks.math.columbia.edu/tag/08KP). Here the equivalent
kernel argument is implemented using the native flat-quotient tensor
equivalence and conservativity after algebra extension.

The original definitions are preserved. The inhabitant theorem is derived
from native proofs and does not assume `EtalePatching` or replace it with a
restricted finite or Noetherian family. Native compilation is evidence for
this formal source; it is separate from the principal's mathematical
adoption and publication decisions.
