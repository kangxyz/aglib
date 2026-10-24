# Killing a small indexed family of maps

`Attachment` constructs the native pushout of the coproduct evaluation
`∐ Aᵢ → K` and `∐ Aᵢ → Cone(id)`. It proves that the original map out of `K`
is monic and constructs an actual nullhomotopy of each original family map.
The family index has an independent universe; only its actual native coproduct
is assumed, not an assumed replacement object or a replacement predicate.

`QuasiIso` uses the generic native pushout/cone comparison and exact-colimit
acyclicity to prove that this original inclusion is a quasi-isomorphism when
all original sources are acyclic. Its exactness assumption is precisely
`HasExactColimitsOfShape (Discrete ι) C`, supplied in particular by AB4 at the
indexing universe, not a finite or boundedness assumption on the complexes.
The comparison retains the original map, and the nullhomotopies are actual
chain homotopies, not merely zero classes in a homotopy category.

The generic `AcyclicColimit` supplier currently imports the existing generic
short-complex colimit comparison from the continuity family. This documented
ownership debt avoids copying or modifying that accepted readonly producer;
a future coordinated relocation can remove the import-layer debt.

`AllMaps` uses Grothendieck local smallness to index all maps from a prescribed
small family by an actual small dependent sum of shrunken hom types. Every
original map has a specified homotopy after the original inclusion. The family
itself is still input, not a supplied detection theorem.

The separate `SmallAcyclic` family now supplies the genuine chosen small
shift-closed tests. Detection and the complete native transfinite replacement
remain separate consumers. One must iterate the genuine attachment with the
injective-factor step and prove the final regular-stage properties. No global
K-injective replacement follows from one successor attachment alone.

The sole compiler accepted `Attachment` and `AcyclicColimit` in graph 021
and the full `QuasiIso`/`AllMaps` consumer closure in graph 022. This is
compilation evidence for the actual successor operation, not final audit
evidence or a proof of global replacement existence.

## Functorial all-maps successor

`IndexFunctor` defines postcomposition on the actual shrunken all-maps index,
then the original coproduct map and its identity/composition/evaluation laws.
`Functor` uses the native identity-cone functor and native pushout map to define
maps of the original all-maps attachments, proving identity/composition and
naturality of the original inclusion. Its unit retains the existing mono/QI
and specified nullhomotopy suppliers. The sole compiler accepted both leaves
in graph 079; this establishes the native successor functor and original
natural mono/QI unit, not global replacement existence. The earlier `AllMaps`
objectwise acceptance alone did not establish functoriality.
