# Nonconstant multiplication and finite curve maps

The invertible-level interface is now supplied by
[MultiplicationInvertible](MultiplicationInvertible.lean), over every field.
This leaf retains its general conditional interface; its theorem premises
are unchanged.

`MultiplicationFinite.lean` proves that an origin-preserving map `f : G.X ⟶ H.X`
between native `Grp (FScheme k)` objects satisfying `Curve.Properties` is
dominant, finite and surjective if `f ≠ 1`. Here `1` is the constant morphism
`toUnit G.X ≫ η[H.X]`, not the identity endomorphism.

The theorem holds over an arbitrary field and uses the literal input map.
Over an algebraic closure, the image of the generic point is either generic or
closed because the target has dimension one. In the second case specialization
makes the map constant on points; the pointed equation identifies that value
with the origin. Reducedness, separatedness and closed-point detection give
equality of scheme morphisms. Faithful scalar extension descends the resulting
nonconstant-to-dominant implication. The existing proper-curve theorem then
supplies finiteness, and proper dominance supplies surjectivity.

`multiplication_pointed` proves that the actual map `(𝟙 G.X) ^ n` preserves the
origin. `multiplication_finite_surjective_of_ne_one` applies the geometric result
to that same map. Its nonconstancy premise is essential to the proved interface;
positivity and invertibility of `n` have not been shown to imply it here.

The target source is the finite conjunct of `EllipticMultiplicationGeometry`,
`R5Lab/AlgebraicGeometry/EllipticCurve/Isogenies/CyclotomicDualKernel.lean:283–286`,
in the supplied packet at R5Lab `f8a3314ddecffcada2ec721d26d56a937bed9690`.
This module is a new partial producer, not an implementation of that theorem
family. It supplies neither the positive-level nonconstancy theorem nor a
geometric degree or a rank-two torsion basis.

Existing mathematical providers are `Curves.SmoothGeometry` (integrality and
pointed rigidity), `Curves.Projectivity.Graph` (the dimension-one dichotomy and
proper-dominant finiteness), `Group.CurveIsogeny` (the native curve adapter), and
`Group.ScalarExtension` (literal group-scheme base change). Mathlib's
`AlgClosed.Basic.ext_of_apply_eq` provides reduced morphism detection.
