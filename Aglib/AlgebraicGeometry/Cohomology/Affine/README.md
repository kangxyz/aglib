# Affine quasicoherent acyclicity and direct image

For every commutative affine ring and actual quasicoherent module sheaf, positive cohomology vanishes without Noetherianity. [Vanishing](Vanishing.lean) supplies `AlgebraicGeometry.Scheme.Modules.AffineDerived.isZero_rightDerived_globalSections_succ`; [SheafCohomology](SheafCohomology.lean) compares the module resolution with the unchanged additive `Sheaf.H` and gives actual affine quasicoherent vanishing. The comparison does not assume that forgetting module injectives preserves injectives.

[GlobalSectionsExactness](GlobalSectionsExactness.lean) gives actual global-section lifting and exactness for the stated quasicoherent-kernel sequences. [DerivedGlobalSections](DerivedGlobalSections.lean) gives the native resolution section-complex and flasque comparison. [PushforwardAcyclicity](PushforwardAcyclicity.lean) supplies `Scheme.Modules.isZero_rightDerived_pushforward_succ` for an actual affine morphism and quasicoherent coefficients, again with no finite/flat/Noetherian premise.

[FirstCohomologyPushforward](FirstCohomologyPushforward.lean) gives `Scheme.Cohomology.affinePushforwardModuleH1Equiv`: structural-field H1 of an actual quasicoherent module sheaf agrees with H1 of its affine direct image. It uses actual section cokernels, coefficient connecting maps and the direct-image resolution sequence; finiteness of the scheme morphism is not required.

Focused imports are the six `Aglib.AlgebraicGeometry.Cohomology.Affine` leaves. Lower [affine scalar comparisons](../../Modules/QuasiCoherent/Affine/README.md), principal-cover Cech exactness and actual injective/flasque interfaces feed the proof route. Cech comparison and field base change consume the resulting vanishing statements.
