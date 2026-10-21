# Regularity descent for essentially etale local maps

[EtaleDescent.lean](EtaleDescent.lean) proves descent on the same actual
`R`-algebra `S`. The two rings may lie in independent universes. The hypotheses
are commutativity, locality and Noetherianness of both rings,
`IsLocalHom (algebraMap R S)`, `Module.Flat R S`,
`Algebra.EssFiniteType R S`, and `Algebra.FormallyUnramified R S`.
There is no characteristic or dimension restriction.

The public declarations lie in `Algebra.FormallyUnramified`:

- `spanFinrank_maximalIdeal_eq_of_flat`: the two maximal ideals have the same
  minimal number of generators.
- `finrank_cotangentSpace_eq_of_flat`: the cotangent spaces have equal
  dimensions over their respective residue fields.
- `isRegularLocalRing_base_of_flat`: regularity of `S` implies regularity of
  `R`.
- `isRegularLocalRing_iff_of_flat`: regularity of `R` and `S` is equivalent,
  combining the new descent with the existing ascent theorem.

Write `m_R`, `m_S` for the maximal ideals and `k_R`, `k_S` for the residue
fields. Flatness makes the canonical multiplication map
`S ⊗[R] m_R → m_R.map (algebraMap R S)` injective; the definition of ideal
extension makes it surjective. Essential finite type and formal
unramifiedness give `m_R.map (algebraMap R S) = m_S`. Consequently,

```text
dim[k_S] (k_S ⊗[S] m_S)
  = dim[k_S] (k_S ⊗[R] m_R)
  = dim[k_S] (k_S ⊗[k_R] (k_R ⊗[R] m_R))
  = dim[k_R] (k_R ⊗[R] m_R).
```

For a finitely generated module over a local ring, its residue-field fiber
dimension is its minimal number of generators. This proves the first two
interfaces. The dimension equality from [Etale.lean](Etale.lean) then
identifies the defining regularity equalities on the two rings.

The proof uses the pinned Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`, specifically
`TensorProduct.spanFinrank_top_eq_of_residueField`,
`TensorProduct.AlgebraTensorModule.cancelBaseChange`,
`Module.finrank_baseChange`, and
`Module.Flat.lTensor_preserves_injective_linearMap`. The maximal-ideal
identity is `Algebra.FormallyUnramified.map_maximalIdeal`; the dimension
supplier is `Algebra.FormallyUnramified.ringKrullDim_eq_of_flat` in
[Etale.lean](Etale.lean).

This module proves the essentially etale case. It does not assert the general
flat-local regularity-descent family. The scheme application is
[Properties/Regular/Descent/Etale.lean](../../AlgebraicGeometry/Properties/Regular/Descent/Etale.lean),
and the interface consumer is
[AglibTest.EtaleRegularityDescent](../../../AglibTest/EtaleRegularityDescent.lean).
