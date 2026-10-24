# Actual affine bidual sections and surface lines

The original affine internal-Hom comparison identifies sections of the
actual dual sheaf with the linear dual of the original section module.
Its scalar map is the original restriction-unit isomorphism followed
by the original affine structure-section isomorphism. Applying this
comparison twice identifies actual bidual sections with the module
double dual.

The exported evaluation equation sends the original sheaf `bidualMap`
to `Module.Dual.eval`. No abstract replacement for internal Hom or an
independently chosen generic scalar occurs.

The structure module is affine-locally quasicoherent of finite type
through its original singleton free presentation. On a locally
Noetherian scheme, the actual internal-Hom coherence theorem then
proves coherence of the dual and bidual of a coherent sheaf.

For the local line conclusion, let the affine coordinate ring be a
regular domain whose prime localizations have dimension at most two.
Suppose the original localization of the source section module has
generic dimension one. Reflexivity of the module double dual and its
actual localizations is derived. The regular-local dimension bound
then gives freeness, and the original localization rank equations give
rank one at every prime.

Finite presentation spreads these singleton bases to principal opens.
The original affine basis comparison and covering construction provide
actual singleton local bases for the restricted sheaf bidual. The
conclusion is `IsLocallyRankOne` for that literal sheaf, with no assumed
reflexivity, line structure, or canonical-module identification.

The current consumer takes the source sheaf to be the raw top exterior
power of relative differentials. Its affine finite quasicoherent
property and generic dimension one must be derived from the original
differentials and their generic basis. This family does not construct
the blowup comparison map or a proper-trace square. It includes the
regular local dimensions zero and one as well as two, and places no
restriction on residue-field separability or characteristic two.
