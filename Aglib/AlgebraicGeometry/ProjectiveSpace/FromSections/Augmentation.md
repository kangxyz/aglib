# Linear augmentation of the original homogeneous coordinates

Let `R` be any commutative ring, let `ι` be an index type in the same
universe, and let `u : ι →₀ R`. In the native namespace
`ProjectiveSpace.FromSections.Augmentation`, `linearForm u` is the
original sum `Σ i, u i • X i`. The family `family u` has this linear
form at `none` and the unchanged `X i` at `some i`.

`presentation u` is the actual degree-one graded polynomial substitution.
`embedding u` is its original `Proj.map`:

```text
ProjectiveSpace R ι → ProjectiveSpace R (Option ι).
```

The retained coordinates span the entire original degree-one component.
The existing `Proj.DegreeOneEmbedding` theorem therefore proves that
this map is a closed immersion. `embedding_toSpec` records its exact
original `R`-structure triangle. No finiteness or nonemptiness assumption
on `ι`, and no flatness, domain, or Noetherianity assumption on `R`, is
introduced.

The public `chartMap u i` is the original homogeneous-localization map
on the target chart `some i` and source chart `i`. It preserves actual
ring coefficients and every retained coordinate ratio. The new ratio is
the original finite sum of coefficient-times-ratio expressions, proved
by `chartMap_ratio_none`. `awayι_comp_embedding` identifies the resulting
affine chart morphism with composition by the actual embedding.

For an original graded `R`-algebra `C` with grading `G`, original family
`g : ι → C`, actual equality `span R (range g) = G 1`, and actual
equalities `(G 1)^n = G n` for every natural `n`, `presentation_comp`
and `embedding_comp` prove composition with the same original
degree-one presentations. The new family is exactly the specified
combination of `g` followed by all unchanged members of `g`.

The public affine consumer is `plainFamily_map_augmentation`. Given
`β : R →+* T`, finite `ι`, and `c : ι → T`, `plainFamily c i` is the
literal original endomorphism of the unit module on `Spec T` given by
multiplication by `(ΓSpecIso T).inv (c i)`. Its epimorphic coproduct map
is an explicit original-family hypothesis. The typed abbreviation
`unitModule T` retains that exact scheme-module object throughout the
frame and section comparisons. For the same supplied
locally-rank-one proof `hunit` used by `mapOfFiniteFamily`, the equation

```text
u.sum (fun i r => β r * c i) = 1
```

proves that its actual finite-family map followed by `embedding u` is
the original `FromSections.AffineChart.map β c`, with coordinates
`(1, c i)`. The proof retains the actual `generatingSectionsOfFamily`
object, uses its proved original-section comparison on each actual
frame, and compares the original chart-ring coefficients and ratios.
The native generating-sections constructors receive the same original
epimorphism proof explicitly through an abstract module boundary.
The coefficient calculation uses the native identity from a structure-ring
component to its unit-module component; it does not require a numeral
instance on an arbitrary module-section carrier.
It does not replace the family by an alternative generating family.

Empty coordinate sets and empty sources remain included. In the affine
consumer, an empty sum equal to one forces the coefficient ring to be
trivial; the native constructions and cover argument retain this case.

The initial implementation input was the read-only, wholly uncompiled
scratch candidate `CoordinateAugmentation.lean`, SHA-256
`01799f2afdcb88f3a59c62ec41969f83472467f8f58bdaf1aa569b0be4ea581a`,
under the contraction author's assigned scratch directory. This source
moves the reusable mathematics to its native projective-section owner,
adds the base triangle, and exposes the actual affine-family consumer.
The contraction row restrictions, scalar Rees chart comparisons, and
global projectivity conclusion remain in their separate owners.

Input basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean `4.34.1`.
