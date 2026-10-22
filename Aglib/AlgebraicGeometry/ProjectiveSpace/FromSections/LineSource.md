# Projective coordinates from an original line-module source

Let `X` be the original scheme over an arbitrary commutative ring `R`, with
original structural map `p : X ⟶ Spec R`. Let `D` and `J` be actual module
sheaves on `X`, both locally rank one. The inputs are the original finite index
`I`, the actual maps `d : I → (D ⟶ J)`, and the epimorphism

```lean
Epi (CategoryTheory.Limits.Sigma.desc d)
```

The scheme, ring and index retain the native common universe. No Noetherian,
field, flatness, properness or separately supplied generation premise is used.

`LineSource.coefficientModule D J` is the existing tensor sheaf
`Dᵛ ⊗ J`, using the actual structure-linear dual of `D`. Its section attached
to an original `d i` is canonical: invert the existing evaluation isomorphism
`Dᵛ ⊗ D ≅ O_X`, then apply the existing dual-tensor functor to `d i`.
`sectionFamily_epi` proves generation from the original epimorphic row by
the native tensor equivalence and its coproduct comparison. It does not choose
frames or replace the original maps by another spanning family.

`LineSource.mapOfFamily D J hD p hJ d` invokes the passed `FromSections`
constructor on this canonical family. `mapOfFamily_toSpec` retains `p`, and
`twistingPullbackIso` identifies the actual pullback of native `O(1)` with
the original coefficient module. `pulledCoordinate` is the pullback of the
original indexed native homogeneous coordinate, before that comparison.

For each original `i`, `pulledCoordinate_triangle` gives the exact unit-section
triangle

```text
evaluation(D).hom ≫ pulledCoordinate i ≫ twistingPullbackIso.hom = F.map (d i)
```

Here `F` is the existing dual-tensor equivalence functor and
`evaluation(D).hom : Dᵛ ⊗ D ⟶ O_X`. Thus the coordinate recovers the original
map under canonical duality. `recoveredCoordinate` applies the existing fully
faithful functor's preimage to this triangle, and `recoveredCoordinate_eq`
proves literal equality with `d i`.

`recoveredCoordinate_coefficient` states the resulting coefficient formula on
any supplied actual frames of `D` and `J`, on any smaller original open: apply
the original `d i` to the source frame's original generator, then take its
coefficient in the target frame. This retains the original maps for later
comparison with rational-function coordinates. No basis, field-valued ratio,
rational map or desired projective morphism is an input to the construction.
