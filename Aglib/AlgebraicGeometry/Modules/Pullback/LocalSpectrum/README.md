# Modules on the original local spectrum

[Germs](Germs.lean) gives the original pullback-unit germ and cancellation
equations for the stalk/local-spectrum section comparison.
[Naturality](Naturality.lean) packages those same component isomorphisms
as natural isomorphisms. It preserves the actual coefficient morphism and
stalk action.

[GenericEmbedding](GenericEmbedding.lean) starts with an integral scheme
and one supplied frame of a module's original generic stalk over its
native function field. It transports that frame through the actual
local-spectrum pullback and defines the original stalk-to-function-field
map with its germ formula. Its injectivity results retain the stated
quasicoherence and torsion-free hypotheses.
Canonical numerator constructions reuse this same frame and embedding.

Present consumers include [Canonical coefficients on embedded normal surfaces](../../../Cohomology/Duality/Projective/Relative/NormalSurface/README.md), [Original canonical trace and local evaluation](../../../Cohomology/Duality/Projective/Relative/NormalSurface/Trace/README.md).
