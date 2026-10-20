# Finite-free Milnor clutching and etale descent

[FiniteFree](FiniteFree.lean), imported as
`Aglib.RingTheory.Etale.MilnorPatching.FiniteFree`, extends
`RingHom.Etale.MilnorPatching`. It identifies the actual boundary quotient and
its map, and proves surjectivity and the exact extended-kernel equation from
the displayed tensor comparison. These boundary statements require no
flatness or Noetherian hypothesis.

`FiniteFree` constructs an explicit stable retraction exhibiting the clutched
module as a retract of a product of two finite free modules. Surjectivity of the original boundary map
supplies matrix coefficient lifts internally; an invertible lift of the
transition is not assumed. For every finite index type, the original
split-power fibre-product map is finite and flat, including nontrivial
endpoint-dependent transitions. The original `finitePresentation_map` retains
its Noetherian hypothesis on the actual fibre base.

[Unramified](Unramified.lean) constructs the canonical tensor algebra
equivalences with both component algebras. Their pure-tensor maps multiply by
the actual first and second projections, with explicit inverse formulas. A
conductor argument shows that tensoring with the two components jointly
detects a zero module. Applying this to the module of differentials proves
formal unramifiedness without assuming flatness of the normalization map.

The stable retraction also proves projectivity. The native module finite
presentation and module-to-algebra comparison then give
`finitePresentation_map_of_surjective` over an arbitrary fibre base. Thus
`FiniteFree.etale_map f g e hf` proves that the original split-power fibre map
is etale when `f` is surjective, the index type is finite, and `e` is the
displayed boundary-algebra automorphism. No Noetherian or characteristic
hypothesis is needed.

The [finite-flat client](../../../../AglibTest/EtalePatching.lean) and
[etale client](../../../../AglibTest/EtalePatchingUnramified.lean) use the two
polynomial endpoints and rotation at one endpoint, for every finite cyclic
level over an arbitrary field. The latter checks both canonical tensor
comparisons and the literal seven-map conductor statement, with the actual
first-projection normalization action on the polynomial ring.

The universal `EtalePatching` family for arbitrary etale component algebras in
[the parent leaf](../MilnorPatching.lean) remains an explicit input. The
split-power theorem does not instantiate that broader family.
