# Original linear twist Ext comparison

[Linear](Linear.lean) refines the sole
`twistingExtCohomologyAddEquiv` to
`twistingExtCohomologyLinearEquiv` for arbitrary commutative rings, integer
twists, natural Ext degrees and the original common geometric universe.
The original `Sheaf.H.{u+1}` and structural scalar actions are unchanged.
`twistingExtCohomologyLinearEquiv_toAddEquiv` is a literal definitional
equality to the old additive equivalence.

The three native linear factors are precomposition by the actual tensor
unit isomorphism, `Adjunction.extLinearEquiv` for the original opposite
twist tensor functor, and postcomposition by original twist multiplication.
They work for every specified structural ring map. The last factor is the
existing native module-Ext/cohomology linear equivalence. Actual tensor
linearity comes from [the lower tensor owner](../../../../Modules/Tensor/Linear.lean).
No field, Noetherianity or finite-generation premise is introduced.

The core source passed `1792124789189888000-74278` at default budgets.
The independent native Ext/large-H consumer and literal old-map check
passed `1792124867769536000-75237`, using the three standard axioms.
The actual tensor-unit and geometric section normalization is a separate
immediate consumer of these same maps.

`twistingExtCohomologyAddEquiv_naturality_right` and its literal linear
refinement retain original coefficient functoriality in every degree. A
map `φ : O(b) → O(c)` induces the actual opposite-twist tensor map,
conjugated by the original multiplication isomorphisms
`O(-a) ⊗ O(b) ≅ O(-a+b)` and `O(-a) ⊗ O(c) ≅ O(-a+c)`.
The result is the original `Sheaf.H.map`, equivalently
`moduleCohomologyMapOfHom` for the same structural action. No new
cohomology map is constructed. The extended leaf passed
`1792129617355406000-21005`; its raw arbitrary-ring consumer, old-map
identity and four axiom checks passed `1792129787016977000-23764`
with only the three standard axioms.
