# The exact kernel of scalar extension of an ideal

Source: [ScalarExtensionKernel.lean](ScalarExtensionKernel.lean).

For commutative rings `S`, `T`, an `S`-algebra structure on `T`, an actual
ideal `I : Ideal S` and `c : I`, the identity

```
algebraMap S T c • z = Algebra.extendedIdealInclusion S T I z ⊗ₜ[S] c
```

holds on the original `T ⊗[S] I`. It is proved once by native tensor
induction and commutativity in the original ideal. The map is the existing
`Algebra.extendedIdealInclusion`, not a replacement image or localization.

If `algebraMap S T c` is regular, the kernel of that map is exactly
`Submodule.torsion T (T ⊗[S] I)`. The forward direction has the displayed
regular annihilator; the reverse direction uses torsion-freeness of `T`
over itself. There are no domain, injectivity, flatness, Noetherianity,
finiteness or local-ring premises.

A geometric consumer must still identify its actual pullback/stalk map with
this original tensor inclusion and derive the mapped element's regularity.
This ring result alone does not construct an invertible image, a blowup,
a normalized chain or a Gorenstein modification.

Direct consumers: [AlgebraicGeometry/IdealSheaf/BaseChange/StalkKernel](../../AlgebraicGeometry/IdealSheaf/BaseChange/StalkKernel.md).
