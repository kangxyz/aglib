# Section localization and quasi-compact open direct image

[AffineSections](AffineSections.lean), imported as `Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSections`, expresses actual section localization through denominator clearing on a quasi-compact open of an affine scheme. The finite-cover argument clears finitely many denominators and overlap relations.

[AffineOpenSections](AffineOpenSections.lean) transports native affine
quasicoherent localization to an actual affine open `V` of any scheme.
The comparison is the original restriction-adjunction unit along
`Spec Γ(X,V) → X`, with its section-ring action and principal-open
restriction square proved explicitly. `toSpecTopSectionsLinearEquiv`
packages the same comparison over the original affine section ring;
its coefficient naturality keeps the actual restricted sheaf morphism.
A section on `X.basicOpen f`
extends after multiplication by a power of `f`; a section restricting
to zero is annihilated by such a power. Quasicoherence is needed only on
the canonical affine chart, with no finiteness or Noetherian hypothesis.

[AffineSectionsPushforward](AffineSectionsPushforward.lean) identifies actual open-immersion direct-image sections with the corresponding intersections with the open range. [AffineSectionsQuasicoherent](AffineSectionsQuasicoherent.lean) proves quasicoherence of the resulting direct image under its quasi-compact affine-open hypotheses; quasicoherence of the pushforward is a conclusion, not an input. [AffineSectionsGlobal](AffineSectionsGlobal.lean) extends the actual open-base-change argument to quasi-compact open immersions and supplies its locally Noetherian variant.

The actual open immersion, compactness and coefficient hypotheses remain attached to each statement. Lower section/localization and geometric restriction maps feed these four leaves. Quasicoherent pullback/gluing, coherent homology and finite-type local comparison consume their results; lower [finite-presentation locality](../../FinitePresentation/README.md) is a separate interface.

The general open direct-image results `quasicoherent_pushforward_open` and `quasicoherent_pushforward_open_of_locallyNoetherian` have the native `Scheme.Modules.QuasiCoherent` owner; they do not belong to the coherent category merely because an earlier source did.

[PrincipalCech](PrincipalCech.lean) owns the actual affine principal-cover
section and cocycle calculations. Its original `AffineCech.Section`,
`res`, denominator bounds and `exists_cechOne_coboundary` retain arbitrary
commutative rings, quasicoherent coefficients and an independent finite
cover-index universe. The implementation was moved without byte changes
from `Cohomology/Cech/AffineDegreeOne`; that old module is a public-import
wrapper. The source SHA-256 before and after the move is
`280eaedf8ce03461dc3c4c9a3f9dbef6602550660e44e71bac8a7db8bcf3f459`.

The lower source passed with receipt `1792113763452696000-4843`, the old
wrapper with `1792113888702105000-7202`, and the independent old/new-import
`PrincipalCechLowerConsumer.lean` with `1792113934128889000-8125`.
The native cocycle theorem uses only the three standard axioms. Ordinary
quasicoherent extension closure consumes this lower section calculation.

[AffineSheafification](AffineSheafification.lean) owns the actual comparison
from any affine module presheaf with a compatible localization seed to the
tilde sheaf of the seed module. In the native `Scheme.Modules` namespace,
`affineSheafificationTildeIso` uses the original principal-open localization
maps, original module sheafification and its original counit.
`affineSheafificationTildeIso_seed` sends each original sheafified seed to
the original tilde section. No field, smoothness, or cohomology import is
needed, and no quasicoherence assumption is imposed on the input presheaf.

This is the sole implementation extracted from the first generic block of
`Modules.Differentials.SmoothRank`, admitted from Aglib revision `40af743`.
The former `SmoothRank` qualified names remain public compatibility exports.
The arbitrary-ring affine relative differential computation and its general
scheme-relative consumer use this lower owner. Source provenance is retained
in the file; only namespace ownership and local instance-binding style changed.
