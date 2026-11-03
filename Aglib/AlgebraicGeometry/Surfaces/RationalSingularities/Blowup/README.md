# Original point blowups of rational surface stalks

[PointNormality](PointNormality.lean) proves normality of the whole
ordinary blowup at a closed point of a stalk-normal scheme when that
original stalk is Nagata, two-dimensional and satisfies
`NormalModificationH1Vanishing`. The local replacement comparison and
unchanged complement retain the original scheme-point blowup.

[DerivedUnit](DerivedUnit.lean) makes its original derived structure unit
invertible for integral normal locally Noetherian ambient schemes, with
the same rational stalk data and an explicit dimension-at-most-two bound
on the blowup source. The local rational H1 and supported R1 arguments
use the actual Cartesian stalk square.

[IdealPowers](IdealPowers.lean) retains maximal-ideal sections, their
original inclusion and powers on the normalized ordinary blowup of a
normal Noetherian Nagata rational local surface. Its generating rows and
section-image induction use the same structural scalar map.
These results propagate supplied rationality; they do not derive it for
arbitrary singular input or prove Gorenstein recognition.

Present consumers include [Original canonical trace and local evaluation](../../../Cohomology/Duality/Projective/Relative/NormalSurface/Trace/README.md), [Actual stages of a supplied normalized-point chain](../../Resolution/NormalizedPointBlowupChain/README.md).
