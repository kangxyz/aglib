# Tilde pullback composition at literal ring maps

Source: [Composition.lean](Composition.lean).

The complete natural and component laws retain the original native tilde
isomorphisms, scalar extension and given spectrum-triangle proof. The public APIs
are `tildePullbackIso_ringHom_comp_hom_of_triangle`,
`tildePullbackIso_ringHom_comp_hom`,
`tildePullbackIso_ringHom_comp_hom_app_aux` and
`tildePullbackIso_ringHom_comp_hom_app`. Their original proofs, independent
universe bounds and actual maps are retained.

The raw natural law is proved through the original scalar and geometric
adjunctions. Private variable-category component lemmas evaluate that complete
law before specialization. The given triangle proof is used in both the native
comparison and the producer, without an assumed square or replacement model.

The [bundled comparison provider](../TildePullback.lean) keeps its original
implementation and imports none of these extensions. Actual raw-view consumers
import this leaf, keeping the new laws outside the stable provider's dependency
boundary.
