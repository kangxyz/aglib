# Generic flatness of module sheaves

Import `Aglib.AlgebraicGeometry.Modules.Flat.Generic.Integral` for generic flatness over an
integral Noetherian base (Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Thm 4.2, p. 19), and
`Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec` for the affine-base form with an explicit
denominator. The conclusions are the pointwise condition of
[`Scheme.Modules.relativeFlat`](../Relative/README.md): the actual stalk `F_x`, restricted
along `f.stalkMap x`, is flat over the base local ring `𝒪_{S, f x}`, for every `x` over the
chosen open.

`exists_nonempty_open_flat_stalk_of_isIntegral`: let `S` be a scheme with `IsIntegral S` and
`IsLocallyNoetherian S`, `f : X ⟶ S` with `LocallyOfFiniteType f` and `QuasiCompact f`, and
`F : X.Modules` with `QuasiCoherent.affineLocallyFiniteType X F` (the defining property of
`Scheme.CoherentSheaf X` when `X` is locally Noetherian). Then some open `U` with
`(U : Set S).Nonempty` has `F_x` flat over `𝒪_{S, f x}` for every `x` with `f x ∈ U`. The
theorem asserts only some nonempty open; the proof constructs it as `S.basicOpen a` for a
nonempty affine open `V` and `a ≠ 0` in the Noetherian domain `Γ(S, V)`. Only local
Noetherianity of `S` is used. Quasi-compactness of `f` cannot be dropped (an unformalized remark): the disjoint
union `X` of all `Spec 𝔽_p` is locally of finite type over `Spec ℤ`, every nonempty open of
`Spec ℤ` contains some `(p)`, and `𝔽_p` is not flat over `ℤ_(p)`, so `𝒪_X` is flat over no
nonempty open.

`exists_nonempty_open_relativeFlat_of_isIntegral` gives the same open in the form
`relativeFlat (f ∣_ U) (F.restrict (f ⁻¹ᵁ U).ι)`: the restriction of `F` to `f ⁻¹ U` is
relatively flat for the restricted morphism, through the native `morphismRestrict_ι` and
`relativeFlat_of_comp_isOpenImmersion`.

`exists_ne_zero_flat_stalk_of_locallyOfFiniteType` is the affine case `S = Spec A`, `A` a
Noetherian domain, with `[CompactSpace X]`: it supplies `a ≠ 0` such that the stalk condition
holds at every `x` with `a ∉ (f x).asIdeal`.
`exists_nonempty_open_flat_stalk_of_locallyOfFiniteType` restates it with the nonempty basic
open `PrimeSpectrum.basicOpen a`.

The proofs cover the source by finitely many affine opens `W` and apply generic freeness
(`Module.Finite.exists_ne_zero_free_localizedModule_away`, see
[GenericFreeness](../../../../RingTheory/GenericFreeness/README.md)) to the actual sections of
`F.restrict hW.fromSpec` over the literal ring map `f.appLE V W _`. The product of the
denominators works for every chart. Three stalk comparisons are proved here:

- `flat_stalk_specMap_of_flat_localizedModule_away`: for `φ : A ⟶ B` and quasicoherent `N`
  on `Spec B`, flatness of `Γ(N)[1/a]` over `A[1/a]` gives flatness of `N_y` over
  `𝒪_{Spec A, Spec.map φ y}` whenever `φ a ∉ y`. It uses the original `fromTildeΓ` and
  `tilde.toStalk` maps and `Module.flat_iff_of_isLocalization` for the base stalk;
- `flat_stalk_of_flat_stalk_restrict` and `flat_stalk_restrict_of_flat_stalk`: the two
  pointwise directions of `relativeFlat_restrict` along an open immersion of sources;
- `flat_stalk_comp_of_flat_stalk_of_isOpenImmersion`: the pointwise converse of
  `relativeFlat_of_comp_isOpenImmersion` along an open immersion of targets.

The focused tests `AglibTest.AlgebraicGeometry.Modules.Flat.Generic.Spec` and
`AglibTest.AlgebraicGeometry.Modules.Flat.Generic.Integral` apply the theorems to
`Scheme.CoherentSheaf` objects; the inspected proofs use only `propext`, `Classical.choice`
and `Quot.sound`. The intended consumer is the flattening stratification on `P^n_A` (plan row
F12, Nitsure Thm 4.3), not yet formalized.
