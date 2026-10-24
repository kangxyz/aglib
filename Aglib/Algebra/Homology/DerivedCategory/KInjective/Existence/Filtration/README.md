# Acyclic source filtrations

This family constructs the source-side acyclic filtration required for the
Stacks 079L detection argument. It does not replace the compatible homotopy
or Hom-complex primitive construction.

- [Pullback](Pullback.lean) constructs, for monomorphisms `a : A ⟶ M` and
  `j : R ⟶ cokernel a`, the actual map from `A` into their quotient pullback.
  Its native kernel universal property gives a short exact sequence and a
  native isomorphism from its cokernel to `R`.
- [Successor](Successor.lean) applies that construction to the fixed actual
  small acyclic family. For a proper monomorphism between acyclic complexes,
  it produces an acyclic intermediate complex, monomorphisms preserving the
  original inclusion, a non-isomorphic first map, and a specified small-family
  representative isomorphic to its cokernel. Properness follows from a
  nonzero separator map into the original quotient.

The assembly retains the entire predecessor diagram at every limit, with
its actual colimit cocone. Filtered-stage acyclicity reuses
`HomologicalComplex.acyclic_colimit` from `Aglib.Algebra.Homology.AcyclicColimit`;
there is no duplicate exact-colimit theorem here. Exhaustiveness is proved
from the small native type of subobjects of the ambient complex, not assumed.
The compatible-primitive construction additionally needs the full predecessor
inverse-limit cone, not just pairwise surjective transition maps.

- [SubobjectStep](SubobjectStep.lean) transports the actual extension to the
  native subobject lattice, retaining strict inequality and the cokernel of
  the canonical `Subobject.ofLE` map.
- [Union](Union.lean) constructs the actual canonical supremum cocone on an
  entire filtered `MonoOver` diagram. Native Grothendieck subobject theory
  supplies its colimit property; the existing acyclic-colimit supplier gives
  acyclicity of the supremum.
- [Growth](Growth.lean) defines a total inflationary operator on all native
  subobjects. Nonacyclic inputs go to top explicitly. Proper acyclic inputs
  grow with quotient in the one fixed shift-closed family. No monotonicity
  of this choice operator is asserted.
- [Stages](Stages.lean) uses native transfinite iteration to construct the
  increasing stages, proves their acyclicity by successor/filtered-limit
  induction, and retains every strict predecessor inclusion and its actual
  limit-stage colimit comparison isomorphism.
- [Exhaustion](Exhaustion.lean) proves that an actual small ordinal stage is
  top by cardinal noninjectivity. It chooses an ordinal index and endpoint
  from this theorem; no exhausted-filtration hypothesis is introduced.

- [Continuity](Continuity.lean) exposes the native underlying complex diagram
  as `IsWellOrderContinuous`. The actual comparison from the entire strict
  predecessor colimit is monic at every stage, including an empty prefix.
- [Colimit](Colimit.lean) retains the canonical cocone of the original
  inclusions into the ambient complex. The actual colimit comparison is mono
  by filtered-subobject theory and epi because one proved stage is top,
  giving a specified native colimit isomorphism to the original complex.
- [Quotients](Quotients.lean) identifies the literal successor maps in the
  coherent diagram. Each is stationary or has its actual cokernel isomorphic
  to a member of the same final shift-closed test family.
