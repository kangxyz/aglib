# Original two-stage homology transport

This owner retains the native homology comparisons for four additive,
homology-preserving functors between four abelian categories, with independent
object and morphism universes. The supplied natural isomorphism compares the
two actual functor composites. No model or replacement homology is introduced.

`homologyMap_twoStage_square` takes four complexes of an arbitrary shape and
the actual cochain arrows d, κ, κ₁, Φ. Its hypothesis is the genuine cochain
square `G(d) ≫ κ₁ = E ≫ G'(κ) ≫ Φ`, where E is the existing native complex
comparison induced by the supplied natural isomorphism. The conclusion is the
corresponding homology square with all original exact-functor comparisons.
It uses the existing `homologyMap_twoStage_exactIso` and original naturality.
Neither κ nor κ₁ nor Φ is required to be invertible, and desired homology
compatibility is not an assumption.

The actual consumer is `canonicalAmbientHomologyScalarMap_counit` in the
parent OpenCounit owner. It supplies its original geometric cochain square
and the native homology-adjunction law. The exact generic source 9f5432be
and consumer 3cd223bb passed selected native graph65 checks at normal limits
(2 and 113 seconds respectively). This is not acceptance of the later
OpenTopClass.Source, source-presentation endpoint, or global gluing.
