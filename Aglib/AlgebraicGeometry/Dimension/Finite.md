# Dimension under finite morphisms

`Scheme.Hom.topologicalKrullDim_le_of_isFinite` is the upstream finite-morphism
dimension theorem. Its original affine-cover proof uses the actual finite
section-ring map and incomparability for integral extensions. Neither scheme
must be nonempty, reduced, Noetherian or of finite dimension, and the morphism
need not be surjective. The public OpenCover import and upstream argument names
are retained.

`Scheme.Hom.stalk_dimension_le_of_finite` bounds the dimension of each original
source stalk by the target dimension. It follows from the native supremum
formula for scheme dimension and that same finite-morphism theorem. It retains
the surface-resolution interface without a second finite-algebra proof.

`Scheme.Hom.topologicalKrullDim_le_of_finite` is a compatibility wrapper for
the same theorem, retained for the quasi-excellent resolution consumers.
The per-stalk wrapper in `Surfaces/Resolution/Necessity` continues to consume
the actual bound. No normality or surface hypothesis enters these general bounds.
