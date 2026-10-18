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

`Basic` also proves `exists_projectiveHilbertFunction_eq_sum_choose`: for coherent `F` there
are integers `a₀, …, aₙ` with `χ(O(r) ⊗ F) = Σ_{i ≤ n} aᵢ C(r, i)` for every `r : ℤ`, where
`C = Ring.choose`. This is the form of the hypothesis of Mumford's bound (Nitsure,
arXiv:math/0504590v1, Thm 2.3, p. 11). Its single induction proves the binomial form: a module
killed by the coordinates in `S` has binomial coefficients only below the number of coordinates
outside `S` (`exists_projectiveHilbertFunction_eq_sum_choose_of_killed`). The step is
`Int.eq_sum_choose_of_fwdDiff` ([RingTheory/Binomial](../../../../RingTheory/Binomial.lean)): a
binomial forward difference integrates to a binomial sum. Polynomiality follows, since binomial
sums are polynomial (`Polynomial.IsPolynomialOnInt.sum_choose`, in `Difference`).

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
`sum_range_alternating_of_long_exact`. The same leaf compares dimensions once, at variable
modules, for the original linear maps `moduleCohomologyMapOfHom` with the structural constants:
`projectiveCohomologyDim_eq_zero_iff` (coherent), `projectiveCohomologyDim_le_of_surjective`,
`_le_of_injective`, `projectiveCohomologyDim_eq_iff_injective` and
`projectiveCohomologyDim_zero_le_of_mono`; `unitHom_eq_zero_of_subsingleton` says that a module
with `H⁰ = 0` has no nonzero global section. Mumford's step consumes them without unfolding
`projectiveCohomologyDim`.

`FieldBaseChange` proves `projectiveCohomologyDim_pullback_map`: for a field extension `k → K`,
finitely many coordinates and a quasicoherent `M` on `P_k`, the cohomology of the pullback along
`ProjectiveSpace.map (algebraMap k K) ι` has the same dimensions. It is the dimension form of
flat base change (`moduleCohomologyTensorMap_isIso_of_isPullback`, with
`ProjectiveSpace.isPullback_map`), the reduction to an infinite field of Nitsure's Lemma 2.1
(p. 10) and Thm 2.3 (p. 12). With `twistingTensorPullbackIso` it gives
`projectiveHilbertFunction_pullback_map`: for a field map `ψ : k →+* K`, finitely many coordinates
and a quasicoherent `G`, the Hilbert functions of `G` and of its pullback along
`ProjectiveSpace.map ψ ι` agree. `Fiber` and Mumford's bound consume it.

`Difference` defines `Polynomial.IsPolynomialOnInt` and proves `of_fwdDiff`: a
polynomial forward difference forces a polynomial function. The antiderivative
comes from Mathlib's `Polynomial.bernoulli_eval_one_add`. The leaf is pure
algebra; its intended owner is a polynomial family under `Aglib.Algebra`.

`TwistMultiplication` uses `twistingTensorMultiply a d s`, defined with its
pure-tensor formula `twistingTensorMultiply_section` in
[ProjectiveSpace/Tensor/Monoidal/Multiply](../../../ProjectiveSpace/Tensor/Monoidal/Multiply.lean).
This is multiplication by a global section `s` of `O(a)` on the twist factor, a natural
transformation from tensoring by `O(d)` to tensoring by `O(a + d)`. The transport lemmas
`twistingSection_eqToHom_val` and `twistingSectionsEquiv_eqToHom` used by this leaf and by
`Coordinate` live in [ProjectiveSpace/Twisting](../../../ProjectiveSpace/Twisting.lean).
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
coordinate `Xᵢ = coordinateSection i` is zero. For a section `s` of `O(1)`,
`frameCoefficient R ι s i hV` is its frame coefficient `s / Xᵢ` on `V ≤ D₊(Xᵢ)`; it commutes
with restriction, is additive and linear over global functions, and is one for `s = Xᵢ`. If `s`
kills `F`, its frame coefficients kill the sections of `F` (`frameCoefficient_smul_eq_zero`), so
`mono_twistingTensorMultiply_of_isSMulRegular` makes multiplication by `s`,
`M ≅ O(0) ⊗ M → O(1 + 0) ⊗ M`, a monomorphism when every frame coefficient is a nonzerodivisor on
the chart sections of `M`. This is the chart side of the general hyperplane of Mumford's bound.

`GeneralHyperplane` proves `exists_forall_frameCoefficient_isSMulRegular`: over an infinite field
and with finitely many coordinates, one section `s` of `O(1)` has frame coefficients `s / Xᵢ` that
are nonzerodivisors on `Γ(Fⱼ, V)` for finitely many coherent modules `Fⱼ` and every subopen
`V ≤ D₊(Xᵢ)` (Nitsure, arXiv:math/0504590v1, p. 10). The chart rings are Noetherian, the chart
sections are finite (`finite_sections_of_affineLocallyFiniteType`), `s ↦ s / Xᵢ` is `k`-linear
with `Xᵢ ↦ 1`, so `associatedPrimes.exists_forall_isSMulRegular`
([RingTheory/Regular/PrimeAvoidance](../../../../RingTheory/Regular/PrimeAvoidance.lean)) applies;
`AffineOpenSections.isSMulRegular_restrict` passes regularity to the subopens.

The induction in `Basic` stays on projective space. It removes one coordinate
at a time through the kernel and cokernel of multiplication by `Xⱼ`. It uses
neither an infinite field, nor associated points, nor a hyperplane section. The
intended owners of the reusable helpers are `Modules/Tensor` (nested section
lemmas; the smul-left lemma `moduleTensorSection_smul_left` already lives in
`Modules/Tensor/Stalk/Bilinear.lean`) and `ProjectiveSpace/Tensor` (the killing class; twist
multiplication `twistingTensorMultiply` already lives in `ProjectiveSpace/Tensor/Monoidal/Multiply`).

Local constancy of the Hilbert polynomial in flat projective families is not
proved here. The fibre over `p` is already identified with
`ProjectiveSpace κ(p) ι` by `ProjectiveSpace.baseChangeIso`
(`ProjectiveSpace/BaseChange/Cartesian.lean`), and the twisting sheaves pull back to the
twisting sheaves along every coefficient base change (`ProjectiveSpace.twistingPullbackIso`,
`ProjectiveSpace/BaseChange/Twisting.lean`). `FieldBaseChange` transports cohomology dimensions
along field extensions only. Still missing here are the transport of cohomology dimensions
along `R → κ(p)` and the relative flatness of the twists.
