# Actual Picard dual and the multiplication-triangle reverse

For every field `k`, an actual finite etale surjective group morphism
`f : E → D`, native curve properties `hE`, `hD`, and the explicit native
hypothesis `Curve.coherentGenus k E.X = 1`, `picardDualHom` constructs an
actual group morphism `D → E` on the original schemes.
`picardDualHom_pointClass` proves, on every test scheme `T`,

```text
A_E(a ≫ picardDualHom f) = f* A_D(a).
```

Here `A` is the original normalized degree-zero Abel class and the
right-hand pullback is literally `f × id_T`. The construction applies the
existing evaluation-divisor inverse on the locally Noetherian scheme
`D.X`; naturality gives the comparison on arbitrary tests. Its origin
identity follows from reduced-source Abel injectivity, and proper-curve
rigidity supplies its group-homomorphism property.

Over an algebraically closed field of arbitrary characteristic,
`picardDualHom_triangle` additionally uses the actual geometric degree
`HasGeometricDegree f.hom.hom n` and proves
`f ≫ picardDualHom f = [n]`.
Consequently `eq_picardDualHom_of_triangle` identifies any actual reverse
`d : D → E` with that source triangle as this Picard dual.
`reverse_pointClass` then proves the actual Picard pullback formula for
the supplied reverse on every test scheme.

The geometric degree enters essentially. Let `I_E` and `I_D` be the
actual identity ideal classes. The class `f*I_D − n·I_E` is proved
degree zero on every geometric fibre, using the input geometric degree
and the native degree of the rational identity divisor. The existing
Abel inverse on `Spec k` realizes this correction as a point class.

For the actual normalized diagonal class `P`, the proved point/divisor
group bridge makes its two evaluations additive. Therefore the
cross-effect

```text
C(L) = -δ*L + pr₁*L + pr₂*[-1]*L
```

vanishes on point classes, while `C(I_E) = P_E`. Cross-effect commutes
with actual group-map pullback. It follows that
`(f × f)*P_D = n·P_E`. The constructed Picard-dual comparison and
reduced-source Abel injectivity give its multiplication triangle.
Only after this geometric proof is epimorphism cancellation applied to
identify the given reverse.

No representing witness, all-test Picard representability, norm family,
square/cube family, or multiplication-triangle identification is assumed.
The explicit native coherent-genus premise must still be supplied. In
particular an old packet's abstract `GeometryBackground.genus_one`
field has not been identified with this native premise here.
The algebraically closed reverse comparison applies to geometric fibres.
[IsogenyPairing](IsogenyPairing.md) uses it to construct the actual kernel
evaluation pairing; its [Galois specialization](IsogenyPairing/Galois.md)
proves the arithmetic action law over the original field.

This is a producer toward `EG-CARTIER-KERNEL-PAIRING`, not the perfect
pairing endpoint. The fixed source is
`packet/sources/lean/R5Lab/AlgebraicGeometry/EllipticCurve/Isogenies/CyclotomicDualKernel.lean`
at R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9e41c9cb806d7b989f7827341fb0c9e54fbcc2276d8f006efcc11b17aedb99a4`.
Its full retained Cartier target has characteristic zero, invertible
positive level, actual degree and both multiplication triangles. The
comparison proved here needs only the source triangle after the genuine
Picard dual has been constructed, over an algebraically closed field.
