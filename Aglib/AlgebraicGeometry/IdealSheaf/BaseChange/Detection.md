# Detection from the original ideal pullback map

`Scheme.Hom.ker_comap_eq_of_idealPullbackMap_epi c i f a h` takes the
original maps `c : D ⟶ Z`, `i : E ⟶ X`, `f : X ⟶ Z`, `a : E ⟶ D`,
their actual equation `h : a ≫ c = i ≫ f`, closed-immersion instances for
`c` and `i`, and epimorphy of the original canonical map

```lean
Scheme.Hom.idealPullbackMap c i f a h
```

It proves the literal equality `c.ker.comap f = i.ker` of the original
`Scheme.IdealSheafData`. No cartesianness or ideal equality is an input.
There is no flatness, Noetherian, coherent, finite-type, line-bundle or
Cartier premise. All schemes have the same universe supported by the native
module and ideal APIs; empty schemes require no separate condition.

The proof constructs the actual standard pullback immersion
`j := pullback.snd c f`. The existing
`idealPullbackMap_epi_of_isPullback` proves that the canonical original map
onto `idealModule j` is epi. Its composite with `idealInclusion j` agrees
with the original supplied map composed with `idealInclusion i`, by the two
native `idealPullbackMap_inclusion` identities. A kernel lift therefore gives
an actual inclusion `idealModule j ⟶ idealModule i` preserving the two
original inclusions into the structure module. Epimorphy of the supplied map
forces this inclusion to be epi; it is also mono, so it is an isomorphism.

The existing `idealSectionsEquiv` identifies the original actual ideal
sections with the kernels of the original section-ring maps. Evaluation of
the inclusion-preserving isomorphism gives equality of those actual kernels
on every affine open, hence equality of the two ideal-sheaf data. The native
standard-pullback kernel formula identifies `j.ker` with `c.ker.comap f`.
No replacement tensor, stalk, ideal-sheaf or closed-subscheme framework is
introduced.

For actual cartesianness, the existing Mathlib endpoint
`AlgebraicGeometry.isPullback_of_isClosedImmersion i c a f h.symm hker`
in `Mathlib/AlgebraicGeometry/IdealSheaf/Functorial.lean` takes the returned
`hker` and gives `IsPullback i a f c`. Its `.flip` is the original orientation
`IsPullback a i c f`. This is a derived consequence, never a premise of the
new equality theorem.

The PointIdeal consumer retains the proof that its original canonical
`idealPullbackMap` is epi, including its actual first-order generation,
finite target stalks and off-image argument. This endpoint supplies only
the final general implication from that exact original-map epimorphism.
