# Fibrewise regular maps from actual line bundles

[Charts](Charts.lean), imported as `Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Charts`, identifies an actual line-bundle-to-unit map with its chosen unit-chart scalar. The actual section image and zero-inclusion kernel are the corresponding principal ideals. Scalar regularity gives monicity; flatness of the actual chart quotients gives flatness of the actual zero-scheme composite.

[GeometricFibre](GeometricFibre.lean) constructs the actual pulled line-bundle map on each categorical field fibre, followed by the canonical unit comparison. `GeometricFibreRegular` is the property of this specified map being monic on every algebraically closed field-valued fibre in the original universe.

[Fibrewise](Fibrewise.lean) supplies `Scheme.Modules.Invertible.mono_and_flat_zeroInclusion_comp_of_geometricFibreRegular`: for an arbitrary flat locally finitely presented morphism, the displayed geometric-fibre property implies monicity of the original map and flatness of its actual zero-scheme composite. The base can be nonreduced and non-Noetherian. The finite coefficient stages and local ring criteria are supplied by the proved ring producer, not a missing theorem-family assumption.

The lower [general module zero-locus data](../../ZeroLocus.lean) preserves its explicit image-localization prerequisites for kernel and image identifications. Quasicoherence proves that condition; for a line bundle it follows from the native local-free structure. [Trivialization](../Trivialization.lean) supplies actual unit-chart coordinates without an integral-scheme premise.
