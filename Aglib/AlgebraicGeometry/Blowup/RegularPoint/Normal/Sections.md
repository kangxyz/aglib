# Original range and Laurent section coefficients

This owner proves the original restriction-frame and Laurent coefficient calculation used
by `RegularPoint.Normal`. It consumes the frozen actual kernel frames in `Normal.Frames`
and the native restriction Hom equivalence. No normal comparison, section-lifting family
or unspecified frame family is a premise of the concrete construction.

The original range frame is constructed from the inverse chart frame through
`rangeRestrictionHomEquiv`. Its coefficient and generator maps retain their original
components. Native adjunction-unit coherence compares further restriction with original
pullback composition. `rangeFrameCoefficientData` has a checked opaque body containing the
literal chartSectionEquiv coefficient and its equality proof; the plain scalar projection
and `rangeFrameCoefficient_eq` retain that original formula.

The canonical module presentation is constructed from the literal native pullback.
`pullbackSectionModuleData f L` has the checked body
`⟨(Scheme.Modules.pullback f).obj L.val, Iso.refl _⟩`. The generic projections expose this
object and its canonical isomorphism to the actual pulled line module before concrete
specialization. Opacity prevents automatic expansion of the implementation; it adds no
mathematical assumption and selects no unrelated line.

`conormalSectionModule` specializes this construction to the actual inverse-image-centre
kernel. `conormalSectionModuleIso` compares it to the actual conormal line.
`conormalSectionChartFrame_hom_original` proves that the transported chart frame, followed
by that canonical comparison, is exactly the original parameter frame morphism.
The generic range-coefficient transport theorem cancels only this module isomorphism.
`conormalOverlapCoefficient_original` therefore recovers the coefficient of the original
actual conormal frames. The upper cocycle uses this equation rather than a forced
judgmental identification of module presentations. The former unaccepted
`conormalSectionModule_eq` interface has been replaced by these explicit original maps.

For the reciprocal charts the hypotheses are CommRing A, I=span{a,b}, a regular on A,
b regular modulo a, and the symmetric two regularity conditions. No Noetherian or local-ring
assumption is added to this general coefficient calculation. `conormalOverlapMap` is the
literal positive Laurent map followed by the original centre chart, with its proved
open-immersion instance. `conormalOverlapOpen` is the original range intersection.
`conormalOverlapCoordinateMap` is its actual appLE followed by the native Spec
global-section isomorphism into LaurentPolynomial(A/I).

`conormalOverlapCoordinateMap_coefficient` proves that the original coefficient is T(1).
`conormalOverlapCoefficient_laurent` recovers the section-valued equation through the inverse
of that same Spec isomorphism. The native frame equation, actual module comparison, original
chart maps and scalar action are all retained. The range-frame recovery proof uses `erw`
only where the native scheme/module presentations require semireducible conversion; no
check is disabled and no new unit object is introduced.

## Native source and coverage

Lean source SHA:
`75d5ddc2a4ac8be50346b78eba9e02a163b840861f37d5e2e945d6c6c090c8c8`.
Its actual frontend passed in 59 seconds in Original run
`remote-13a19a804a194f31bf75e68c604e5333`, SOURCE
`1375fb371689f028bc72fa2ccf0e8f7fd9dafe42166f7db3ed10ab205fe0020f`.
The matching full Normal consumer also passed. The combined graph exited 1 solely because
an independent PointIdeal target failed; this is a scoped module success, not a whole-run
success. Earlier failed candidates are not used as successful evidence.

Only `conormalOverlapCoordinateMap_coefficient` retains the explicitly authorized,
explained declaration-local maxHeartbeats800000 setting. Every helper and the package
default remain 200000; the optional helper400000 grant was never used. This exact source
passed at the retained setting. Frozen Frames2677 and the earlier actual P1/ideal providers
were reused unchanged. This guide was finalized after the run; the compiled Lean bytes
remain unchanged. No additional native validation, replay or positive-provider run was made.
