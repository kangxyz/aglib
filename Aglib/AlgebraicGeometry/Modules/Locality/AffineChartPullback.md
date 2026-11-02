# Original affine-chart pullback coefficient map

Source: [AffineChartPullback.lean](AffineChartPullback.lean).

`restrictFunctorIsoPullback_inv_unit_app` proves the original inverse
restriction/pullback comparison preserves the original adjunction unit. It uses
the existing uniqueness of left adjoints and the same native isomorphism.

`affineChartRestrictionLinearMap_pullback` computes the scalar-adjoint
coefficient arrow of the original pullback chart comparison as exactly
`affineChartRestrictionLinearMap`. Its proof uses the preceding unit law and
naturality of the original `pushforwardGlobalSectionsIso`.

The charts, ring map, chart triangle, module and scalar actions are arbitrary
original inputs. No quasicoherence, finite presentation, localization, target
invertibility, trace square or geometric finiteness is assumed. No new Hom
reconstruction or module model is introduced. The genuine finite-cover consumer
is `FiniteCoverTrace/AffineRestriction.lean`.
