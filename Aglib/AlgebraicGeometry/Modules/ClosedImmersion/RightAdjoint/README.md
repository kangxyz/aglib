# Computing the single selected closed right adjoint

[Affine](Affine.lean) identifies sections of the original ordinary
`closedImmersionRightAdjoint` for a closed spectrum map `Spec S → Spec R`
with the native `ModuleCat.coextendScalars` of the original R-sections.
This natural isomorphism is in `ModuleCat S`, hence retains the actual
S-action for every target coefficient sheaf N; N need not be quasicoherent.
The original `tildePushforwardIso` identifies the left adjoints, and native
right-adjoint uniqueness identifies these same right adjoints.

`closedImmersionRightAdjointAffineIso_unit` and `_counit` retain the native
composite adjunction maps. `_homEquiv` compares the original geometric
Hom-adjoint with the original scalar-coinduction adjoint through that same
tilde-pushforward map. The linear section formula is
`Γ_S(i!N) ≃ Hom_R(S, Γ_R N)` with its actual coinduced action:
`(b • h)(b') = h(b' * b)`. Its displayed scalar equation does not assume
quasicoherence of an injective resolution term. The native open restriction interface is now proved in
[Restriction](Restriction.lean), using the original extension-by-zero
exchange and native conjugation of the actual adjunctions. Its unit, counit
and Hom-adjoint equations hold for every coefficient sheaf. No arbitrary
stalk/internal-Hom interchange is used.

[The parent right-adjoint leaf](../RightAdjoint.lean) owns ordinary existence,
additivity and preservation of injectives. The generic
[K-injective adjunction](../../../../Algebra/Homology/DerivedCategory/KInjective/Adjunction/README.md)
discharges both K-injectivity conditions at bounded-below injective targets.
The local Koszul Ext calculation and canonical-bundle identification consume
these original maps; no derived full faithfulness of closed pushforward is
asserted.

`closedImmersionRightAdjointOpenIso` has the original `f!` followed by
source-open restriction as its source, and target-open restriction followed
by the original base-changed `b!` as its target. The public consumer derives
closedness of `b` from the supplied Cartesian square and closedness of `f`;
no QC, Noetherianity or finite-presentation condition is introduced.
