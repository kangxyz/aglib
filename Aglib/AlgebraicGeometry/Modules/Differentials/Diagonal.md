# Diagonal conormal and native differentials

`Aglib.AlgebraicGeometry.Modules.Differentials.Diagonal` imports the canonical
map `Diagonal.differentialToConormal p` from its affine provider. It is induced
by the coordinate difference
`p₂* a - p₁* a` in the original diagonal ideal. Its codomain is the actual
module-sheaf pullback of `idealModule (pullback.diagonal p)`.

For any scheme map `p : X ⟶ Spec R`,
`Diagonal.differentialToConormal_affineBase_isIso` proves that this same map is
invertible; `Diagonal.conormalIsoOfAffineBase R p` is its inverse isomorphism.
No smoothness, separation, finiteness, reducedness, or field premise is required.
The proof identifies the original affine tensor-kernel class with the native
Kähler differential, proves source-open naturality of the canonical map, and
detects invertibility on the actual affine source cover. Existence of unrelated
local isomorphisms is not used as a substitute for this compatibility.

The forward affine formula sends `1 ⊗ a - a ⊗ 1` to the original `D(a)`.
The genus consumer is `Aglib.AlgebraicGeometry.Group.CurveGenus`. The global
comparison here is stated for affine bases; an arbitrary-base extension is not
part of this module's interface.
