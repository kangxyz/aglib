# Original coefficient unit and section equations

`Sections.lean` imports Model and owns the original base-ring unit
specialization, finite H0-to-sections comparisons, augmentation equations,
and the actual global-section tensor isomorphism. Its forward arrow remains
the literal `moduleTensorTildeSectionsMap`, not an abstractly chosen map.

The component proofs retain the original bottom inclusion, finite inclusion,
extension-by-zero comparison and section augmentation. The final invertibility
argument uses the existing quasi-isomorphism in the sharp range
`-(n : ℤ) ≤ d`. Coefficients remain arbitrary modules over any commutative
base ring; no Noetherianity or coefficient-flatness premise is introduced.
The original finite-coordinate, dimension and universe inputs are unchanged.

All five private helpers move together with their consumers. Their compiler
private-name module prefix changes, but no helper is made public and no proof
body is altered. The existing generic component-pasting lemma is reused.
The two original named derived-category instances are locally activated from
Model; no additional realization is constructed. This leaf does not import
Naturality, and the old Coefficients owner publicly reexports the complete
section interface.

An actual downstream consumer is Derived/CoefficientsTopHom, which uses
`twistingTensorTildeSectionsIso`. Its current transitive import through
TwistExt/Coefficients and the old facade remains unchanged by this packet.

## Status

This split leaf is source-reviewed preparation, not a compiled result. Native
acceptance remains pending. Complete-family isolation is not a demonstrated
memory cure or speedup, and no failing declaration has been identified by the
aggregate RSS guard.
