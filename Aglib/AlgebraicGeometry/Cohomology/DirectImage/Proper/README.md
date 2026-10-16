# Proper coherent higher direct images

[Coherent](Coherent.lean) proves
`Scheme.Modules.moduleHigherDirectImage_coherent_of_proper`: every original
`(pushforward f).rightDerived q` sends a coherent coefficient to a coherent
sheaf for a proper map with locally Noetherian target. The target need not
be quasi-compact, and the coefficient need not be relatively flat.

The proof descends the actual affine-base
[proper finiteness theorem](../../Proper/Finiteness.lean) along target affine
charts. It uses the original
[higher-image open comparison](../Restriction.lean) and the native affine
finite-sheaf comparison. There is no new cohomology construction or supplied
proper-finiteness family. The arbitrary-universe public consumer checks the
proper and finite specializations; the inspected theorem uses only the
three standard axioms. A uniform global derived upper bound on a target
that is not quasi-compact is not claimed by this interface.
