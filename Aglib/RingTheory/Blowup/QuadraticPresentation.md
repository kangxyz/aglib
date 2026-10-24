# Quadratic tangent cones and actual exceptional presentations

The original three ideal generators and the full Hilbert function determine a
nonzero homogeneous quadratic generating the entire canonical tangent-cone
kernel. Its original dehomogenization presents the exceptional quotient of the
literal saturated blowup chart. Every original coefficient and fraction map is
retained. The main theorem is `CaseOne.exists_presentation_of_hilbert`.

## Exact final contract

Let `A` be a commutative local ring, `m = maximalIdeal A`, and `k = ResidueField A`.
Fix the original ordered triple

```
g₀ = t, g₁ = g 0, g₂ = g 1,
```

where `t : m` and `g : Fin 2 → m`. The first genuine input is the literal ideal
identity

```
Ideal.span (Set.range fun i => (orderedGenerators t g i : A)) = m.
```

The second is the full Hilbert function of the original associated graded ring,
with its original quotient coefficient action:

```
∀ n, Module.finrank k (Ideal.associatedGradedQuotientGrading m n) = 2 * n + 1.
```

These are the only additional hypotheses of the final producer. In particular,
there is no supplied quadratic, full-kernel equality, cone isomorphism,
exceptional-chart isomorphism, residue-rationality statement, square-membership
conclusion, regularity conclusion, or tangent-square hypothesis.

The theorem `CaseOne.exists_presentation_of_hilbert` returns a literal
polynomial `q : MvPolynomial (Fin 3) k` such that:

1. `q ≠ 0` and `q.IsHomogeneous 2`;
2. the entire kernel of the ORIGINAL canonical map is `Ideal.span {q}`;
3. the original denominator `(t : A)` is nonzero;
4. `Q = q(1,U,V)` is nonzero and has total degree at most two;
5. `CaseOne.Presentation A t g Q` is inhabited.

Here the original canonical map is exactly

```
(Ideal.cotangentPolynomialMap m (Fin.cons t g)).toRingHom.
```

Its coefficient action is the native action of `A/m` on the original Rees
quotient, and it sends `X i` to the original degree-one numerator of `gᵢ`.
The output `Presentation` therefore concerns the literal saturated chart
`C = A[m/t]` and its original principal exceptional ideal, not an abstract local
model. The reduction's exact kernel is additionally proved to be that principal
ideal in `presentationOfKernel_reduction_ker`.

No Noetherianity, domain, or normality premise is needed for this algebraic
producer. The CaseOne local argument still uses its genuine Noetherian
and domain hypotheses. Rationality, Gorenstein duality, normality of ordinary
blowups, and the derivation of the displayed full Hilbert function remain
separate upstream obligations. Those geometric assertions are not conclusions of this algebraic file.

## Obtain a genuine nonzero quadratic relation

Use the six distinct exponents

```
2e₀, 2e₁, 2e₂, e₀+e₁, e₀+e₂, e₁+e₂.
```

The map from `k⁶` to the degree-two component sends the original coefficient
vector `a` to the original canonical image of

```
q(a) = a₀V² + a₁S² + a₂T² + a₃VS + a₄VT + a₅ST.
```

Each of its six original coefficients recovers `aᵢ`, so `a ↦ q(a)` is injective.
All six monomials are homogeneous of degree two. The original target component
has dimension five by the actual Hilbert hypothesis; its finite-dimensionality
also follows from this positive finite rank. Rank-nullity supplies a nonzero
coefficient vector in the displayed linear map's kernel. Thus a nonzero
original quadratic relation is derived, rather than assumed.

Only `H(2)=5` is used for this step. Actual ideal generation separately gives
surjectivity of the full original graded polynomial map through
`Ideal.cotangentGradedPolynomialMap_surjective`.

## Normalize, apply MonicQuadratic, and undo the actual change

The coefficient order throughout is `(V²,S²,T²,VS,VT,ST)`. Every coordinate
change below is an actual polynomial algebra equivalence. Its inverse is
written explicitly, and both directions preserve degree one and hence every
homogeneous component.

| Change | New coefficient vector |
|---|---|
| swap `V,S` | `(a₁,a₀,a₂,a₃,a₅,a₄)` |
| swap `V,T` | `(a₂,a₁,a₀,a₅,a₄,a₃)` |
| replace `S` by `S+V` | `(a₀+a₁+a₃,a₁,a₂,2a₁+a₃,a₄+a₅,a₅)` |
| replace `T` by `T+V` | `(a₀+a₂+a₄,a₁,a₂,a₃+a₅,2a₂+a₄,a₅)` |

If a square coefficient is nonzero, an appropriate swap puts it first. If all
three square coefficients vanish, a nonzero `VS` or `VT` coefficient gives a
nonzero first coefficient after the corresponding shear. In the remaining
case the `ST` coefficient is nonzero; swap `V,S` and then shear `T` by `V`.
This argument works over every field, including characteristic two; it never
divides by two or uses polynomial-function faithfulness over a finite field.

Consequently there is a constructed equivalence `E` and a coefficient vector
`b` with `b₀ ≠ 0` and `E(q(a)) = q(b)`. Define

```
q₁ = b₀⁻¹(b₃S + b₄T),
q₀ = b₀⁻¹(b₁S² + b₂T² + b₅ST).
```

The literal identity is

```
V² + q₁(S,T)V + q₀(S,T) = C(b₀⁻¹) * E(q(a)).
```

For the original graded map `π`, use `π' = π ∘ E⁻¹`. This is a constructed
surjective graded map to the SAME original target and grading. Its displayed
monic relation vanishes. The genuine `H(n)=2n+1` hypotheses therefore apply
directly to `GradedAlgebra.MonicQuadratic.kernel_eq_span`.

For an original `p ∈ ker π`, the actual image `E(p)` lies in the derived monic
principal kernel. Apply the actual inverse `E⁻¹` to that divisibility identity.
It gives `p ∈ (q(a))`. The reverse inclusion follows from the already-derived
original relation `π(q(a))=0`. This proves the full original kernel equality.
The final kernel and quotient map therefore retain the original ordered
parameters. The temporary polynomial change is completely undone; no
coefficient-field section or lifted matrix over `A` is selected.

This implements the normalize/apply-MonicQuadratic/undo route described
above, with the full kernel recovered through the original coordinate maps.

## Dehomogenize through the actual Rees quotient

Let `G` be the original associated graded ring and `f` the original degree-one
symbol of `t`. Existing native `reesAlgebra.exceptionalChartEquiv` gives

```
C/(t) ≃ HomogeneousLocalization.Away G f.
```

The native degree-one quotient comparison gives `Away G f ≃ G/(f−1)`.
The canonical map has `π(X₀)=f`, with the original numerator equality proved.
Using the derived original full kernel, ordinary quotient comparisons give

```
G/(f−1)
  ≃ (k[V,S,T]/(q))/(V−1)
  ≃ (k[V,S,T]/(V−1))/(q)
  ≃ k[U,V]/(q(1,U,V)).
```

The middle equivalence is the native commutation of two ideal quotients. The
last is the original `finSuccEquiv` followed by evaluation at one; its exact
kernel is `(X₀−1)`. No flatness or projectivity fact is used.

Every original polynomial `p` is sent, through this composition, from the
class of `π(p)` to the class of `p(1,U,V)`. Applying this identity to original
coefficients and to `X₁,X₂`, and composing with the existing Rees numerator
laws, proves exactly

```
[a] ↦ [C(residue A a)],
[g 0 / t] ↦ [X 0],
[g 1 / t] ↦ [X 1].
```

These are the two fields of the `CaseOne.Presentation` record in addition
to its equivalence. Their actual map construction is carried in the implementation,
not supplied as a compatibility premise.

The six quadratic exponents dehomogenize to the six distinct affine exponents

```
0, 2e₀, 2e₁, e₀, e₁, e₀+e₁.
```

Their coefficients are still exactly `aᵢ`. Since `a ≠ 0`, the actual `Q` is
nonzero; each displayed exponent has degree at most two. Finally, if the
original `t` were zero, `X₀` would lie in the full canonical kernel `(q)`.
A nonzero homogeneous quadratic cannot divide the nonzero degree-one variable
in the polynomial domain. Thus the original denominator is nonzero as well.

## Native owners and implementation boundary

The source basis is the release checkout
`f27c5fa9b8f76147e16caacf52f56f26eabddb87`, Lean `4.34.1`, and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The load-bearing native suppliers are:

- `AssociatedGraded/Cotangent/Graded.lean`: the original coefficient action,
  canonical symbol map, graded map, and surjectivity from actual ideal generation;
- `GradedAlgebra/MonicQuadratic.lean`, `kernel_eq_span`: the full kernel from the
  genuine monic relation and all original target Hilbert dimensions;
- `ReesAlgebra/ExceptionalChart.lean`, `exceptionalChartEquiv`,
  `exceptionalChartEquiv_mk_base`, and `exceptionalChartEquiv_mk_fraction`:
  the actual saturated exceptional quotient and its original maps;
- `GradedAlgebra/HomogeneousLocalization/DegreeOne.lean`:
  `degreeOneQuotientEquiv` and the original numerator formulas;
- Mathlib `Ideal/Quotient/Operations.lean` and `Polynomial/Ideal.lean`:
  the original quotient-kernel equivalence, commutation of two quotients, and
  the kernel of evaluation at one;
- Mathlib `LinearAlgebra/FiniteDimensional/Lemmas.lean`:
  the actual six-to-five dimension argument;
- `Blowup/CaseOne.lean`: the exact `Presentation` record and its conditional
  local singularity, original residue-map, and exceptional-parameter results.

The underlying mathematical route is the explicit normalization, monic-kernel,
inverse-coordinate, and Rees-dehomogenization argument given above. Its
conditions are part of the theorem. The geometric source of the Hilbert
function, rationality, Gorenstein duality, and normality of ordinary blowups
remain upstream. Later Case-I nonsquare propagation, uniqueness, and marked
continuation are separate consumers.

At final assembly, the residue algebra and component modules are selected
directly from the original quotient action and original quotient-graded
submodules. They are constructions of the existing instances, not new premises
or an alternative scalar action. The genuine ideal-generation hypothesis is
explicitly retained as a proof input to the final theorem. Its mathematical
contract and all original maps are unchanged.
