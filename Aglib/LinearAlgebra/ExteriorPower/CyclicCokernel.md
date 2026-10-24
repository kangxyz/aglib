# Exterior images with a cyclic annihilated cokernel

Let `R` be a commutative ring and `f : P →ₗ[R] Q` a map of arbitrary
`R`-modules. Suppose that each `v : Q` can be written
`v = f(p) + a • q`, and that `π • q` belongs to the original image of `f`.
Then

```text
π • α ∈ LinearMap.range (exteriorPower.map n f)
```

for every `n : ℕ` and every `α : ⋀[R]^n Q`. This is
`exteriorPower.smul_mem_range_map_of_cyclic_cokernel`.
It uses Mathlib's existing exterior powers and original exterior map.
There is no finite-generation, free-module, or torsion-free premise.

The image of `f` together with `q` spans `Q`. The native spanning theorem
for exterior powers therefore reduces the proof to wedges whose entries
are image elements or `q`. If every entry is in the image, choose their
original preimages. If two entries outside the image occur, both are `q`,
so the wedge is zero by alternation. If exactly one occurs, move `π` into
that slot and use `π • q ∈ range f`.

The all-image case includes the empty wedge, so degree zero is covered
without any nonempty-index hypothesis. The repeated-entry argument uses
the alternating relation itself and does not divide by two. Thus the
statement also applies in characteristic two and to modules with torsion.

The current consumer is the one-pole estimate for the ordinary
surface-point blowup differential comparison. At the exceptional DVR,
the actual relative differential quotient is a one-dimensional residue-field
module. Lifting its generator gives `q`, and an exceptional uniformizer
kills its class. The theorem then bounds the pole of the original top
exterior map. Reflexive extension, the exceptional twist, derived
pushforward and normalized proper trace remain separate geometric steps.
