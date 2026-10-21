# Singleton bases of actual closed-immersion stalk kernels

[StalkKernel.lean](StalkKernel.lean) owns the generic localization, basis
spreading, and gluing argument shared by [RegularSurface](RegularSurface.lean)
and [Factorial](Factorial.lean).

`Scheme.Hom.idealModule_isLocallyRankOne_of_stalkKernelBasis` assumes a locally
Noetherian ambient scheme `X`, an actual closed immersion `i : C ⟶ X`, and

```text
∀ c : C, Nonempty (Basis PUnit (X.presheaf.stalk (i c))
  (RingHom.ker (i.stalkMap c).hom)).
```

It concludes `IsLocallyRankOne X (Scheme.Hom.idealModule i)`. The hypothesis
supplies bases of actual ring-map kernels. The proof constructs local bases
and canonical comparisons for the actual scheme ideal module. The source
scheme `C` need not be integral, reduced, or nonempty.

The public comparison `Scheme.Hom.ker_stalkMap_eq_map_ker_app` requires only
closed immersion and an affine target open `U`. It identifies the actual
stalk-map kernel with the image of the actual section kernel under the canonical
structure-sheaf germ:

```text
ker(i.stalkMap c) = ker(i.app U).map(germ U (i c)).
```

Its proof identifies both actual stalks as prime localizations of their affine
section rings. The germ/stalk-map naturality equation identifies the localized
section map with `i.stalkMap c`; localization of ring-map kernels gives the
stated ideal equality. This comparison does not require Noetherianity.

For each prime on an affine target chart, the proof transfers a supplied basis
through this ideal equality if its point lies on the closed image. Otherwise,
the section kernel contains an element outside the prime, so its localized
image contains a unit and is the unit ideal. This ideal also has a singleton
basis.

The section kernel is finitely presented by Noetherianity of the affine section
ring. `Module.FinitePresentation.exists_basis_localizedModule_powers`, applied
to the canonical map `Algebra.idealMap`, spreads each basis to a principal open.
`Scheme.Hom.affineIdeal_rankOne_of_localizedBasis` identifies the associated
module sheaf with the actual spectral kernel module. Finally, the canonical
`toSpecΓ` isomorphisms, `idealPullbackMap`, and restriction comparisons give
local rank one on `X`. The inclusion throughout is the actual
`Scheme.Hom.idealInclusion i`.
