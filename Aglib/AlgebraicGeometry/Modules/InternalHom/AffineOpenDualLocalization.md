# Original dual coordinates on actual affine opens

Source: [AffineOpenDualLocalization.lean](AffineOpenDualLocalization.lean).

`AffineOpenDualLocalization.lean` proves a complete actual-open dual restriction
law and compares it with the original named affine dual/bidual coordinates.

## Interfaces

- `affineRestrictionUnitSectionsEquiv_affineOpen` identifies the existing unit
  coordinate with the existing scalar-compatible `affineChartΓIso`.
- `affineDualSectionsEquiv_affineOpen_apply` identifies the existing named affine
  dual evaluation with `InternalHom.affineSectionsEquiv` on the actual affine open.
- `affineDualCoordinate_affineOpen` and `affineBidualCoordinate_affineOpen`
  retain an arbitrary original module coordinate through the same Gamma maps.
- `affineDualCoordinate_restrict` derives native Hom localization of the actual
  dual restriction from restriction of its source coordinate. The proof uses
  `affineSectionsEquiv_restrict` and `IsLocalizedModule.linearMap_ext`.

The localization theorem allows arbitrary localization submonoids of the actual
large coordinate ring, and arbitrary original coordinate modules in unrestricted
universes. It needs quasicoherence of the source on the two original charts,
not finite presentation or quasicoherence of the target. Finite presentation is
used only by the downstream second-dual application to make the first native
Hom localization itself a localized-module map.

No original sheaf, coefficient action, chart map or coordinate definition is
replaced. The bidual coordinate comparison does not assume a restriction law.
The actual bidual-form target square is proved in
`IntegralTrace/AffineOpenBidualRestriction.lean`, rather than left as an abstract
pairing premise. The held broad affine-forms localization owner is not imported.
