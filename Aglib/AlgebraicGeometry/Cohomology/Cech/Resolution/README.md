# Module-valued Cech resolution comparisons

[Basic](Basic.lean) constructs the native `ModuleCat R` bicomplex
`moduleCechResolution X α U I` from the original structural-ring section
presheaf, the original Cech functor, and a supplied injective resolution
`I` in `X.Modules`. The Cech degree is first and the resolution degree is
second. No injectivity after forgetting the module structure is assumed.

`moduleCechColumnAugmentation` uses the original coefficient inclusion
`I.ι.f 0`. `moduleCechRowAugmentation` uses the original restriction
augmentation from top presheaf sections. `moduleCechToTotal` and
`moduleResolutionSectionsToTotal` map the original Cech complex and the
actual native global sections of `I.cocomplex` to the same native total
complex. The latter uses the shared `moduleTopSectionsFunctorIso` from
[native resolution sections](../../DirectImage/ResolutionSections.lean),
whose component is the original `moduleTopSectionsIso`, the identity on
underlying sections.
Both component formulas retain the original total coproduct injections.
Both maps and both augmentations are natural in every actual lift of an
original module coefficient morphism. These constructions require no
covering, quasicoherence, affineness or flatness hypothesis.

[Exact](Exact.lean) proves that these same two maps are quasi-isomorphisms.
`moduleResolutionSectionsToTotal_quasiIso` requires only that the opens
cover the scheme. Its row proof uses injectivity in the original module
category. `moduleCechToTotal_quasiIso` requires a quasicoherent coefficient
and affine intersections for every finite Cech tuple; no covering premise
is needed for that column statement. The positive column proof uses
sections of the supplied actual module injective resolution on each affine
open and exactness of module products. Degree zero uses native left
exactness. Neither statement needs a finite cover, flatness, a Noetherian
base or finite generation.

[Plus](Plus.lean) extends these same complexes and arrows by zero to the
integers and retains their native lower bounds. `moduleCechComplexPlus`
has the original integer Cech complex as its underlying complex.
`moduleResolutionSectionsToTotalPlus` starts at the termwise image of the
actual `I.cochainComplexPlus`. It factors as the native
`moduleResolutionSectionExtendIsoPlus.hom`, followed by the original
extended section augmentation. Both maps remain quasi-isomorphisms under
the corresponding hypotheses above, and their original coefficient/lift
squares remain equalities of actual bounded-below chain maps.

[Derived](Derived.lean) localizes that genuine chain zigzag and constructs
`moduleCechDerivedGlobalSectionsIso X α U I hcover haff`. Its direction is
from `Q.obj (moduleCechComplexPlus X α U M)` to the installed
`(moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus` at the
original degree-zero single of `M`, using the native standard derived
categories in universe `u + 1`. It requires exactly quasicoherence, a cover
and affine finite tuple intersections. The cover may be infinite.

`moduleCechDerivedGlobalSectionsIso_hom_expanded` records the forward map
as the original localized extended Cech augmentation, the inverse of the
original localized extended section augmentation, the inverse native
global-sections/zero-extension comparison, and the actual
[`InjectiveResolution.rightDerivedFunctorPlusIso`](../../../../Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/InjectiveResolution.lean).
That final factor is literally the installed derived unit followed by the
inverse derived image of `I.ι'`. The coefficient-naturality theorem uses
the original module morphism and every supplied native resolution lift.
The underlying Cech complex is definitionally the original integer Cech
complex, so the original finite truncation inclusion can be prepended
directly. No conclusion about perfectness is inferred from a comparison
of cohomology groups alone.
