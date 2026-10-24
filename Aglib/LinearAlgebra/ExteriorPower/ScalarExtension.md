# Exterior powers and scalar extension

For commutative rings R and S, an R-algebra structure on S, and any R-module M,
`tensorBaseChangeEquiv` identifies the actual modules

```text
⋀[S]^n (S ⊗[R] M) ≃ₗ[S] S ⊗[R] (⋀[R]^n M).
```

The forward map comes from a directly constructed exterior-algebra tensor map
and the native homogeneous component. The inverse comes from the original
vector map `m ↦ 1 ⊗ m`. Their formulas and inverse identities are proved on
spanning pure wedges. Degree zero and characteristic two are included.
No flatness, finiteness, or invertibility of two is assumed.

`mapAlgebra` specializes the existing `mapSemilinear` construction with its
actual restricted scalars. The generic `LinearMap.ofAlgebraSemilinear`
constructor preserves the underlying function; `mapAlgebra_apply` expresses
that equality before specializing to native exterior generators.
`isBaseChange_mapAlgebra` and
`isLocalizedModule_mapAlgebra` prove the corresponding properties of the
original exterior map; they do not accept a comparison or compatibility map
as an extra premise.

The direct construction does not require two to be invertible. Its consumer
is the monogenic differential trace and its localization equation: the
exterior comparison supplies the scalar-extension and localized-module
instances for the same Kähler exterior map.
