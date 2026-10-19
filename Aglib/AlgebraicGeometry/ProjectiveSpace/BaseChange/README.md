# Base change of polynomial projective space

The Cartesian entry module is `Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange`.
It proves that the actual polynomial `Proj` commutes with every coefficient
ring homomorphism. The base rings and coordinate type lie in the common
scheme universe; there is no finiteness, flatness, Noetherianity or nonempty
coordinate hypothesis.

- `Map` uses the native `Proj.map` of `MvPolynomial.gradedMap`. Its identity,
  composition and inverse-image formulas retain the original coefficient
  morphism and standard chart opens.
  `map_comp_map_eq_of_comp_eq` turns two factorizations `g.comp f = g'.comp f'` of one ring map
  into `map g ι ≫ map f ι = map g' ι ≫ map f' ι`.
- `Charts` identifies its original homogeneous-localization ring maps with
  the polynomial coefficient maps under the existing chart equivalences.
  It proves the exact equation with the original structural maps to spectra.
- `ChartPullback` proves the original chart-ring square is a pushout and
  identifies both the resulting affine Cartesian square and the actual
  inverse-image chart square.
- `Cartesian` uses the original coordinate affine cover to prove
  `isPullback_map`. The resulting `baseChangeIso` maps to Mathlib's native
  pullback by exactly `pullback.lift (map f ι) (toSpec S ι) (map_toSpec f ι)`.
  Both original projection equations are public.
- `ToSpec` records that `baseChangeIso f ι` lies over the new base:
  `ProjectiveSpace.baseChangeIso_inv_toSpec` (`(baseChangeIso f ι).inv ≫ toSpec S ι` is the second
  projection) and its global-section form `ProjectiveSpace.baseChangeIso_hom_appTop_comp` for the
  structural ring maps through `Scheme.ΓSpecIso`. It is a sibling leaf, so that the widely
  imported `Cartesian` is unchanged.
- The separate focused import `Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Affine`
  identifies any supplied original Cartesian square over a spectrum
  with polynomial projective space over that spectrum's ring. The comparison
  is the native uniqueness isomorphism of the two pullback squares, with
  both forward and inverse projection equations. No open-immersion premise
  is needed for this geometric comparison.
- The separate focused import `Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.AffineOpen`
  treats `X_S = P^n_A ×_{Spec A} S` (`pullback (toSpec A ι) s`) for a scheme `s : S ⟶ Spec A`.
  Over an affine open `U` of `S`, `affineBaseMap ι s hU : P^n_{Γ(S, U)} ⟶ X_S` exhibits
  `P^n_{Γ(S, U)}` as the base change of `X_S ⟶ S` along `hU.fromSpec`
  (`isPullback_affineBaseMap`, with the ring map `affineBaseRingHom s hU : A →+* Γ(S, U)`), and
  for `W ≤ U` the restriction is the base change along `Γ(S, U) → Γ(S, W)`
  (`affineBaseMap_restrict`). For `g : T ⟶ S`, `pullbackBaseChange ι s g` exhibits
  `P^n_A ×_{Spec A} T` as the base change of `X_S ⟶ S` along `g`
  (`isPullback_pullbackBaseChange`); over affine opens `V ≤ g ⁻¹ U` it is the base change along
  `g.appLE U V` (`affineBaseMap_pullbackBaseChange`). `X_S` is locally Noetherian for finitely
  many coordinates and locally Noetherian `S` (`isLocallyNoetherian_pullback_toSpec`). It is a
  sibling leaf, so that the widely imported `Cartesian` is unchanged; the flattening
  stratification over a locally Noetherian base consumes it.
- `Twisting` proves that the twisting sheaves commute with every coefficient base change:
  `twistingPullbackIso φ ι d : π^* O_R(d) ≅ O_S(d)` for `π = map φ ι`. It applies
  `Modules/Invertible/Gluing/Pullback` to the coordinate cocycle. The inverse images of the
  standard charts are the standard charts, and `appLE_coordinateTransitionOn` matches the
  transition units. On every chart subopen the isomorphism sends the pulled-back frame `Xᵢ^d`
  to the frame `Xᵢ^d` (`twistingPullbackIso_hom_generator`, `_inv_generator`, `_inv_app`).
  `twistingTensorPullbackIso` gives `π^*(O_R(d) ⊗ M) ≅ O_S(d) ⊗ π^* M` from the canonical tensor
  comparison; it is natural in `M` (`twistingTensorPullbackIso_hom_naturality`, `@[reassoc]`).
- `Flat` proves that `map f ι` is flat for a flat ring map `f` (`flat_map`): by `isPullback_map`
  it is the base change of `Spec S → Spec R`. The projection of a field extension is flat as an
  instance (`flat_map_algebraMap`), so pullback along it preserves monomorphisms. The structure
  morphism `toSpec R ι` is flat by `ProjectiveSpace/Flat` (`flat_toSpec`).

The lower algebraic owner is
[`RingTheory/MvPolynomial/GradedMap`](../../../RingTheory/MvPolynomial/GradedMap.lean).
Relative projective projections use this scheme comparison to apply the
proved coherent cohomology theorem after restricting the base to an affine
open. The twisting pullback `Twisting` is not a premise of the Cartesian theorem.
