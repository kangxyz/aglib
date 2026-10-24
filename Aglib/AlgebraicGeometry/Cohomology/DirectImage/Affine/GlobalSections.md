# Original global sections after affine direct image

For an affine morphism `f : X → Y` and a quasicoherent coefficient `M`,
`moduleDerivedGlobalSectionsAffineSingleIso` compares the installed derived
global sections of the ordinary `f_* M` with those of `M`. The base action
on the source is any specified `α : R → Γ(Y, O_Y)`, and the action on the
target is literally `f.appTop ∘ α`. The target scheme need not be affine.
No properness, flatness, Noetherianity or coefficient finiteness is assumed.

The construction uses the existing coefficient-specific affine acyclic
single comparison and the inverse of the original derived composition
isomorphism. Its forward arrow is proved to be the image of the original
direct-image single unit followed by that same inverse. The single-unit and
coefficient-unit theorems retain the actual section isomorphism, the
original coefficient arrow and both installed units. The naturality theorem
preserves every morphism of quasicoherent coefficients.

`moduleAffinePushforwardCohomologyLinearEquiv` takes homology and uses the
existing supplied-resolution comparison to the unchanged additive
`Sheaf.H`. It is linear for the specified structural actions. In a
geometric square, the caller must prove the equality of the induced action
with its prescribed action; an unrelated scalar identification is not used.

The current consumer is the finite-diagram comparison in the separable
surface H1 bound. Finite morphisms are affine, so the result applies to the
original structure coefficient upstairs. It does not construct that finite
diagram, its ordinary field-normalized trace or a global H1 bound. It does
not assert exactness of direct image on all module sheaves. Equality of the
cohomology equivalence with a separately constructed geometric
`moduleCohomologyMapAlong` is a distinct map comparison, not a premise or a
claim of this module.

The existing [affine-target higher-image comparison](Cohomology.lean)
concerns a general quasi-compact quasi-separated morphism to a spectrum;
the present result instead uses an affine morphism to an arbitrary target.
Both retain their original objects. Lower sources are
[the affine single comparison](Single.lean),
[derived global-sections composition](../../Functoriality/GlobalSectionsComposition.lean)
and [original cohomology from supplied resolutions](../ResolutionSections/Derived.lean).
