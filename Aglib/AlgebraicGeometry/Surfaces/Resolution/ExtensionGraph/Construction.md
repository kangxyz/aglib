# Actual complementary graphs and punctured H1 injectivity

`Scheme.Cohomology.structureH1_puncturedRestriction_injective_of_isNagata`
proves injectivity of the original structural H1 map to the inverse image
of the punctured spectrum. The base is a normal Noetherian Nagata local
domain of dimension two. The original map `f : X → Spec A` is proper and
dominant, `X` is integral and normal, and the original function-field map
of `f` is invertible.

`structureH1_puncturedRestriction_injective` gives the complete-base
corollary. It derives the initial Nagata property from
`IsNagataRing.of_complete_local_dimLE_two` on the original complete local
ring. Normality of an arbitrary local ring is never used to assert Nagata.

For a class killed by the original restriction, [OpenKernel](../../../Cohomology/Modules/Ext/OpenKernel.md)
constructs a short exact representative with its original Ext/H1 class
and an actual retraction on the original open over-site. Put

```text
V = f⁻¹(localPuncturedSpectrum A)
tau = complementarySection ≫ quotientComplement.ι
W = tau.image
p = tau.imageι ≫ projectiveBundle.projection.
```

The literal triangle `tau.toImage ≫ p = V.ι` makes `p` dominant and its
original field map invertible. The graph is integral and proper over `X`.
For `q = p ≫ f`, each nonempty actual affine open `U` of `W` has scalar map

```text
(q.appLE top U le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom.
```

Its finite type comes from the original affine section map. Dominance
and restriction make it injective. The original germ square and the
original birational field map identify each chart element with `a/s`;
the nonzero polynomial `sX-a` proves algebraicity for exactly that scalar
action. Native
`IsNagataRing.of_finiteType_isAlgebraic_of_dimLE_two` is applied to these
actual data. No affine chart Nagata oracle is a hypothesis of either
public H1 theorem.

Normalize the literal generic inclusion:

```text
gamma = W.fromSpecStalk (genericPoint W)
N = gamma.normalization
nu = gamma.fromNormalization.
```

[Normalization/FunctionField](../../../Normalization/FunctionField.md)
then supplies normality, integrality, the original birational field map,
and finiteness of this actual `nu`. The map into the original projective
bundle is exactly `nu ≫ tau.imageι`.

Finite dominance supplies a point over the original complementary
section, hence generic avoidance. The complementary section is closed
over `V`, so the graph adds no quotient-section intersection over that
open. Its actual pullback intersection is vertical over the original
closed point. The [conditional graph theorem](../ExtensionGraph.md)
then splits the original extension. Its canonical class, and therefore
the original H1 kernel class, is zero.

The public extension-level interface is
`RankTwoExtension.splitting_of_punctured_complementary_section`.
All graph, chart-scalar and support helpers are private to this consumer.
The original projective bundle, image, generic inclusion, normalization,
ideal/conormal argument, field maps and H1 restriction remain the actual
native ones.

[ResidueVanishing](../../../Cohomology/Proper/ResidueVanishing.md) uses this
original punctured H1 injection to construct a lift of the closed-fibre
quotient and obtain the residue-field derived-Hom vanishing. The later
canonical-module comparison, geometric Grauert–Riemenschneider vanishing
and full resolution construction remain separate obligations.
