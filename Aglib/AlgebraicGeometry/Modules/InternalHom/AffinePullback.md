# Original affine Hom maps under pullback

Source: [AffinePullback.lean](AffinePullback.lean).

This focused corollary leaf imports the existing affine Hom constructor and
original affine scalar/pullback counit theorem. Both provider files remain
unchanged. No new Hom equivalence, tilde construction, coefficient map or
pullback comparison is defined.

`counitHomEquiv_symm_counit` reconstructs the SAME inverse of
`counitHomEquiv` after the original source counit, giving the left adjoint of
the supplied map followed by the original target counit. The categories have
independent object and hom universes. Only the source counit is invertible;
the proof uses the existing constructor, native Hom-adjunction counit formula
and native isomorphism cancellation, not the right-adjoint image equation.

`affineGlobalHomEquiv_symm_counit` is its thin specialization to the original
tilde/Gamma adjunction and native ModuleCat Hom equivalence. Only the source
sheaf is quasicoherent; the target is arbitrary.

`affineGlobalHomEquiv_symm_pullback` fixes an arbitrary original ring map
`phi : R -> S`, source sheaves P and P' on the two affine spectra, arbitrary
target sheaves Q and Q', and arbitrary actual arrows

- u : pullback(phi)(P) -> P';
- v : pullback(phi)(Q) -> Q'.

Only P and P' are quasicoherent. For original ModuleCat arrows q and q', the
hypothesis is a square of their genuine scalar-adjoint section maps: Gamma of
the original geometric unit followed by pushforward of u or v and the original
`pushforwardGlobalSectionsIso`. From this coefficient square the theorem proves
that pullback of the SAME inverse affine Hom map at q, followed by v, equals u
followed by the SAME inverse affine Hom map at q'. There is no flatness,
Noetherianity, finite-presentation, open-immersion or epi/iso premise on u or v.

The proof applies native scalar-adjunction square naturality, reuses
`tildePullbackIso_counit` twice, and uses the literal naturality of the SAME
`tildePullbackIso`. It cancels only the inverse tilde/pullback comparison followed
by pullback of the original source counit. It does not prove a Gamma-map equation
for either reconstructed sheaf arrow or use such an equation as an input.
The coefficient maps occur as original expressions and local lets, not as a
second named affine-mate backend.

A finite-cover application still supplies its actual raw, bidual,
localization and normalization coefficient square. The adjunction laws
alone do not give gluing or the original generic trace-functional identity.
