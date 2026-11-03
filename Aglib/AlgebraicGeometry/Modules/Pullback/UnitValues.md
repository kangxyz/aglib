# Original pullback-unit values at variable schemes

`UnitValues.lean` imports only existing `Unit`. It exposes the equality-transport,
inverse-composition, and coefficient-naturality unit equations through native
`Hom.app ⊤` values for arbitrary schemes and module coefficients in their
original universe. It adds no quasicoherence, flatness, affineness or other
hypothesis and retains every original scheme map and equality proof.

The first two statements directly use `pullbackCongr_unit_top` and
`pullbackComp_inv_unit_top`. The third evaluates the existing adjunction-unit
naturality equation. Mathlib defines `Hom.app` by forgetting scalars from the
same `.val.app` component; conversion is performed here with variable schemes,
not after inserting affine spectra. This is not a new model or backend.

The immediate consumer is the arbitrary-presentation affine sheaf composition
proof's `hδ`, `hπ`, and `hn` values. Existing `Unit`, its other importers, and
accepted affine unit/extensionality suppliers are unchanged.

This native-output boundary extraction is structurally justified, but it is not
an identified cause or cure for the consumer's kernel-memory failures. Source
staging is not native acceptance, and no speedup is asserted.
