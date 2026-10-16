# Native adjunction at injective-complex targets

[InjectiveComplex](InjectiveComplex.lean) discharges both K-injectivity
conditions in [the parent adjunction](../Adjunction.lean) for a supplied
bounded-below complex of injectives. The left adjoint needs only to preserve
monomorphisms; its right adjoint therefore preserves injectives. The pure
`isKInjective_map_of_injectiveComplex` needs no derived category or enough
injectives. The actual derived Hom equivalence retains independent object,
morphism and derived-model universes, and both original chain-adjoint
formulas. It requires no upper term bound, quasicoherence or preservation of
injectives by the left adjoint.

The ordinary closed-immersion right adjoint and the affine tilde/sections
adjunction are the present consumers. Installed right-derived unit
normalization remains the responsibility of their supplied-resolution models;
this pointwise Hom equivalence does not introduce a second derived functor.
