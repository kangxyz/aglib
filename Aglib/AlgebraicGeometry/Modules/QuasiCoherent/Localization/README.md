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
