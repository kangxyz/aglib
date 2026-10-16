# Actual quasicoherent extensions

[AffineSections](AffineSections.lean) proves actual affine section lifting
and short exactness when the kernel coefficient is quasicoherent. The
middle and quotient module sheaves are unrestricted. The statements use
the original `moduleSpecΓFunctor`, original section maps, finite principal
local lifts, actual kernel-valued cocycles and original gluing. There is
no ring Noetherianity or nontriviality premise.

The sole implementation was moved from
`Cohomology/Affine/GlobalSectionsExactness`, whose old path is now a public
import wrapper. All declaration names, maps and hypotheses are unchanged;
the only implementation edit was replacing its old principal-Cech import
with the sole lower owner. The original source SHA-256 is
`84fdb01dd61a2b7224479d66cfc0ba9929bce2253d64a031162c2720c8794be2`;
the new import-adjusted source SHA-256 is
`d210a4923deefa5c6b12bd17410ba2e6a903db711090c7adada59db977bf1376`.
Original contributor and license notices are retained.

`shortExact_globalSections_of_quasicoherent_kernel` is the key ordinary
provider for the canonical tilde-counit extension argument. It does not
presuppose quasicoherence of the middle sheaf. The lower source passed with
receipt `1792114003002607000-9876`, the old wrapper with
`1792114063619122000-11070`, and the independent old/new-import
`AffineSectionExtensionLowerConsumer.lean` with
`1792114091925141000-11584`. Its three inspected lift, epi and exactness
declarations use only the three standard axioms.

[Affine](Affine.lean) proves the genuine extension statement. The
`isIso_fromTildeΓ_middle_of_shortExact` theorem uses the original three
counits as a morphism from the actual tilde/global-section short exact
sequence to the original sequence. The native short five lemma makes the
middle counit invertible, so `quasicoherent_middle_of_shortExact` concludes
quasicoherence without presupposing it. `affineFiniteSheaf` is then proved
extension-closed over every commutative ring, since the actual finite
global-section modules are extension-closed. No Noetherianity is needed.

The affine extension source passed with receipt
`1792114252443682000-14865` in 2.6 seconds. Its independent
`QuasicoherentAffineExtensionConsumer.lean` passed with receipt
`1792114318840486000-16551`, checking the literal middle counit and the
arbitrary-ring object-property instance. All four inspected declarations
use only the three standard axioms.

[Global](Global.lean) applies the affine result to the original exact
restriction on every affine chart. It proves
`Scheme.Modules.isQuasicoherent_middle_of_shortExact` and extension closure
of `QuasiCoherent.affineLocallyFiniteType X` for every scheme `X`. The
middle sheaf is unrestricted in the input. These extension statements do
not impose local Noetherianity; interpreting finite-type quasicoherent
sheaves as coherent retains the existing locally Noetherian guard.
Neither predicate is claimed to be a Serre class inside all module
sheaves: arbitrary subsheaves need not be quasicoherent.

The global source passed with receipt `1792114365446795000-17662` in
2.2 seconds. `QuasicoherentGlobalExtensionConsumer.lean` passed with
receipt `1792114430848477000-19022`, checking arbitrary schemes and the
guarded coherent interpretation. All four inspected declarations use only
the three standard axioms. Native coherent-homology triangle closure can
combine this extension result with kernel and cokernel closure of maps
between known coherent objects.
