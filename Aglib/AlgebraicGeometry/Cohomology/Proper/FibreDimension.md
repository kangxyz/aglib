# Original cohomology above the closed-fibre dimension

For a Noetherian commutative ring `A`, an ideal `I`, and
`IsAdicComplete I A`, let `f:X→Spec A` be an actual proper morphism and
`M` the original coherent module, expressed by
`affineLocallyFiniteType X M`. If the actual first ideal thickening

```
Modules.idealThickeningSpace f I = X ×_Spec A Spec(A/I)
```

has topological Krull dimension at most `d`, then the original
`Sheaf.H (moduleAddSheaf X M) q` vanishes for `q>d`.
`subsingleton_moduleCohomology_of_complete_of_dim_firstThickening` states
this on the original cohomology carrier.
`isZero_moduleCohomology_of_complete_of_dim_firstThickening` states it as
zero in the module category with the unchanged structural action
`f.appTop.hom.comp (ΓSpecIso A).inv.hom`.

The module uses the proved native complete-base formal-functions
equivalence and the proved Noetherian cohomological-dimension theorem.
No coefficient flatness, vanishing premise, formal-functions family,
projectivity, coefficient field, or chosen replacement cohomology module
is an input.

The actual thickening immersion for `J⊂A` has range `f⁻¹(V(J))` by the
original pullback-carrier and quotient-spectrum maps. For every positive
power, `V(I^n)=V(I)`. The two actual closed embeddings therefore identify
the underlying spaces of the positive and first thickenings. They are
homeomorphic as spaces; the nonreduced schemes are not asserted isomorphic.
Properness over the Noetherian base makes the actual thickenings Noetherian.
Grothendieck dimension vanishing applies to each original additive sheaf
of the actual pulled-back coefficient, without a flatness requirement.

The native geometric cohomology tower is indexed by all natural numbers,
including zero. Positive coordinates are zero by dimension vanishing.
Coordinate zero is also forced to be zero by its actual transition from
coordinate one. The native complete-base formal-functions equivalence is
linear for the original structural action and sends classes to their actual
geometric restrictions. Its injectivity gives the stated original vanishing.
Proper coherent finiteness and completeness of the original finite module
are already proved inside that equivalence.

`closedFibre_dim_le_one_of_integral_source` treats the actual closed fibre
of a dominant map from an integral source `X` with
`topologicalKrullDim X≤2` to a local domain. It requires that the original
closed point be nongeneric. The fibre is a closed subset of the original
source missing its unique generic point, so the native closed-subspace
dimension theorem gives dimension at most one. The first maximal-ideal
thickening is the actual closed fibre through its original closed immersion.

`subsingleton_moduleCohomology_of_complete_surface_modification` specializes
to a complete Noetherian local domain with `ringKrullDim A=2`, an actual
proper dominant map from an integral source of dimension at most two, and
`q>1`. The closed point is nongeneric because its actual stalk is `A`; if
it were generic, `A` would be a field and have dimension zero. Normality and
birationality may be present in the surface consumer, but this theorem only
needs their stated domain and dominance consequences.

The actual source dimension bound is retained explicitly. The target bound
in the existing finite-length H1 theorem is not substituted for it. The
current consumer is `Surfaces/Birational/Cohomology`; this lower module has
no import from a surface theorem. Its generic-point, closed-subspace and
closed-stalk suppliers are imported directly.

The mathematical sources are [Stacks 02OC, Theorem 30.20.5](https://stacks.math.columbia.edu/tag/02OC)
and [Stacks 02UZ, Proposition 20.20.7](https://stacks.math.columbia.edu/tag/02UZ).
This higher-cohomology bound does not assert H1 or
Grauert–Riemenschneider vanishing. [DerivedStructure](DerivedStructure.md)
uses it in the original unit-preserving Postnikov and low-degree Leray
constructions. [FibreDimension.Local](FibreDimension/Local.md) gives the
corresponding general local-base theorem without completeness.
