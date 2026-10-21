# Structural first cohomology from two affine opens

`Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.StructuralFirstCohomology`
constructs `Scheme.Cohomology.structuralH1EquivTwoAffineQuotient`. Its inputs are
a field `k : Type u`, an actual `X : FScheme k`, opens `U V : X.left.Opens`,
proofs that both opens are affine, and `U ⊔ V = ⊤`. Its output is an actual
`k`-linear equivalence

```text
Scheme.coherentH1 k X ≃ₗ[k]
  Γ(X.left, U ⊓ V) / (range(res_U) ⊔ range(res_V)).
```

The maps `res_U` and `res_V` are
`structuralRestrictionLinearMap X inf_le_left` and
`structuralRestrictionLinearMap X inf_le_right`. Their underlying functions
are exactly the original presheaf restrictions along the two inclusions into
the overlap. `structuralSectionModule X W` is the abbreviation
`Module.compHom _ (Scheme.constantSection X W)` for every open `W`; it does
not replace the structural field action. Its instance is local to this leaf.
Consumers can install it for `U`, `V`, and `U ⊓ V`, or use the definitionally
equal explicit `Module.compHom` instances.

`structuralOpenH0LinearEquiv` identifies native degree-zero open cohomology
with original sections. It is linear because coefficient multiplication by
the original structural constant becomes multiplication by that same constant
on sections. `structuralOpenH0LinearEquiv_restriction` retains the original
restriction maps. Thus the range of the native signed Mayer–Vietoris
difference becomes the sum of the two literal restriction ranges; the sign
does not change a range submodule.

The existing structural Mayer–Vietoris sequence from
[`Scalars`](Scalars.lean) supplies exactness. Actual affine-open vanishing of
`Sheaf.H'` from [`Cech.Comparison`](../Cech/Comparison.lean) makes its first
connecting map an epimorphism. Therefore first open cohomology is the
cokernel of the original difference. The cover equation identifies the union
with the whole space, and `structuralOpenTopLinearEquiv` compares back to the
original `Scheme.coherentH1`, including its original structural action.

There is no affineness hypothesis on `U ⊓ V`, no separatedness, Noetherianity,
properness or finiteness assumption on `X`, and no desired-equivalence family
input. The scalar field and the scheme use universe `u`; the original
cohomology retains its standard Ext universe `u + 1`, while the quotient of
sections lies in universe `u`. Linear equivalences permit these different
universes without a resizing premise.

The immediate consumer is the Weierstrass two-chart genus computation. Its
chart localizations, comparisons with actual sections, and final Laurent
quotient calculation remain in that consumer. This leaf provides the general
structural cohomology comparison only.

Source basis: Aglib HEAD `3a4d549981ced306d89d3ed55418c9e6a25f86c4`, Lean
4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Native
compilation evidence is returned separately for the actual source hashes.
