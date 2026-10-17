# Hilbert polynomials on polynomial projective space

`Basic` proves `Scheme.Cohomology.isPolynomialOnInt_projectiveHilbertFunction`.
For a field `k`, a coordinate labeling `ι ≃ Fin (n + 1)` and a coherent
(`affineLocallyFiniteType`) module `F` on the actual polynomial projective space
`ProjectiveSpace k ι`, the Hilbert function `projectiveHilbertFunction k ι F`
satisfies `Polynomial.IsPolynomialOnInt`. The Hilbert function is
`m ↦ χ(O(m) ⊗ F)`, with the native tensor twist. So some `Φ : ℚ[X]` gives
`χ(O(m) ⊗ F) = Φ(m)` for every integer `m`, negative integers included
(Stacks, Tags 08AC and 08AD; Nitsure, arXiv:math/0504590v1, §1, p. 4).
Arbitrary universes and dimension zero are included.
`projectiveHilbertPolynomial k ι F : ℚ[X]` is that polynomial.
`projectiveHilbertFunction_eq_eval` proves that it computes `χ(O(m) ⊗ F)` at
every integer, and `projectiveHilbertPolynomial_eq_of_eval` proves that it is the
only such polynomial. It is invariant under isomorphism and additive on short
exact sequences of coherent modules. `Difference` supplies the uniqueness, since
two rational polynomials that agree on all integers are equal.

`EulerCharacteristic` defines `projectiveCohomologyDim` and
`projectiveEulerChar`: the alternating `finsum` of the dimensions of the original
`Sheaf.H`. The structural `k`-action is `projectiveConstants`, through `toSpec`
and `ΓSpecIso`. Native `finrank` and `finsum` are zero outside finite dimension
and finite support. For quasicoherent modules the cohomology vanishes above `n`
(`projectiveCohomology_subsingleton_of_gt`, `Cohomology/Projective/Vanishing.lean`),
so the characteristic is the finite sum over the degrees `q ≤ n`. For coherent
modules every cohomology module is finite-dimensional
(`projectiveCohomology_finite`, `Cohomology/Projective/Finiteness.lean`), so the
terms are genuine dimensions. It is invariant under isomorphism and vanishes on zero
modules. `projectiveEulerChar_add_of_shortExact` proves additivity on short exact
sequences of coherent modules (Stacks, Tag 08AA). Its inputs are the original
long exact sequence, H⁰-injectivity, rank-nullity and the telescoping identity
`sum_range_alternating_of_long_exact`.

`Difference` defines `Polynomial.IsPolynomialOnInt` and proves `of_fwdDiff`: a
polynomial forward difference forces a polynomial function. The antiderivative
comes from Mathlib's `Polynomial.bernoulli_eval_one_add`. The leaf is pure
algebra; its intended owner is a polynomial family under `Aglib.Algebra`.

`TwistMultiplication` constructs `twistingTensorMultiply a d s`. This is
multiplication by a global section `s` of `O(a)` on the twist factor, a natural
transformation from tensoring by `O(d)` to tensoring by `O(a + d)`.
`Scheme.Modules.moduleTensor_nested_hom_ext_of_line` proves that morphisms out of
`L ⊗ (M ⊗ N)` are determined by nested pure tensors when `L` is a trivialized
line bundle. `twistingTensorMultiply_app_tensor_eq_zero` proves that if `s` kills
`O(d) ⊗ F`, it kills `O(e) ⊗ (O(d) ⊗ F)` for every `e`.

`Coordinate` defines `IsKilledByTwistSection a s F`: every twist multiplication
by `s` vanishes on `F`. The class is closed under subobjects, quotients and
twists, and vanishing at twist zero suffices. `twistingTensor_nested_hom_ext`
restricts the nested extension to the subopens of the coordinate charts. On
those subopens `s` is its frame coefficient `σ` times the generator, and
`σ • t = s · t₀` for a section `t₀` of `O(0)`. This proves `of_cokernel`: the
cokernel of `s : F → O(a + 0) ⊗ F` is killed by `s`. `of_comp_eq_zero` treats
the kernel. `isZero_of_coordinate_eq_zero` proves that a module killed by every
coordinate `Xᵢ = coordinateSection i` is zero.

The induction in `Basic` stays on projective space. It removes one coordinate
at a time through the kernel and cokernel of multiplication by `Xⱼ`. It uses
neither an infinite field, nor associated points, nor a hyperplane section. The
intended owners of the reusable helpers are `Modules/Tensor` (nested section
lemmas; the smul-left lemma `moduleTensorSection_smul_left` already lives in
`Modules/Tensor/Stalk/Bilinear.lean`) and `ProjectiveSpace/Tensor` (twist multiplication and
the killing class).

Local constancy of the Hilbert polynomial in flat projective families is not
proved here. The fibre over `p` is already identified with
`ProjectiveSpace κ(p) ι` by `ProjectiveSpace.baseChangeIso`
(`ProjectiveSpace/BaseChange/Cartesian.lean`). Still missing are the pullback
formula for the twisting sheaves along that isomorphism, the transport of
cohomology dimensions along it, and the relative flatness of the twists.
