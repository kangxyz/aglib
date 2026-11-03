# The original stalk epimorphism under pullback

Source: [StalkEpi.lean](StalkEpi.lean).

Import `Aglib.AlgebraicGeometry.Modules.Pullback.StalkEpi`.
The namespace is `AlgebraicGeometry.Scheme.Modules`.

`epi_moduleStalk_pullback_of_epi_moduleStalk` takes arbitrary schemes,
the original morphism g, an actual source point z, and an original map
phi between arbitrary module sheaves on the target. Its only epimorphism
hypothesis is on the ORIGINAL target stalk at g(z). It concludes epimorphy
of the ORIGINAL pulled-back map at z. It does not require global epimorphy
of phi, flatness, quasicoherence, finiteness or geometric regularity.

The proof uses the existing pullbackModuleStalkIso with its original scalar
homomorphism `(g.stalkMap z).hom`. Native extension of scalars is a left
adjoint and preserves epimorphisms. Naturality identifies the SAME map,
and native epi transport across the actual iso component gives the result.
No category, tensor, stalk, localization or scalar-action model is rebuilt.

The source imports only the existing lower pullback/stalk provider and native
functor epimorphism machinery. Its proposed consumers are the actual one-point
canonical-map induction and the exact supported local v-stalk pullback, but
neither higher theorem is constructed or assumed here. Point-equality transport
and original pullback-triangle isomorphisms remain the higher caller's data.
