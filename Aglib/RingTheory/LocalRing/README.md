# Local rings

[ParameterAvoidance](ParameterAvoidance.lean), imported as `Aglib.RingTheory.LocalRing.ParameterAvoidance`, proves the positive-dimensional Noetherian local-ring avoidance step: a first minimal generator can be chosen outside every minimal prime. The separate prime-parameter domain result retains the actual principal-prime and avoidance hypotheses; regularity is not assumed for those lower lemmas.

[ParameterQuotient](ParameterQuotient.lean) lifts a nonzero cotangent vector to a minimal generating family containing the specified parameter. For a Noetherian local ring with cotangent-space dimension at most `d+1` and `x` in the maximal ideal but not its square, `IsLocalRing.spanFinrank_maximalIdeal_quotient_parameter_le` bounds the quotient maximal-ideal generator number by `d`, using the stated local-ring instance on the quotient. No regular-local premise is used. The regular quotient and exact dimension-drop endpoint is separately implemented in [RegularLocalRing/ParameterQuotient](../RegularLocalRing/ParameterQuotient.lean).

Native owners follow the actual local/regular-local mathematical subject. These two parameter leaves feed [regular-local domain/parameters/normality](../RegularLocalRing/README.md). Their source statements preserve the nonzero cotangent, dimension and generator conditions used by the induction.

[SeparatedPrincipal](SeparatedPrincipal.lean), imported as `Aglib.RingTheory.LocalRing.SeparatedPrincipal`, treats a local ring with a specified principal maximal-ideal generator. A finite bound on maximal-ideal order yields a unit-power factorization; Hausdorff separation yields such a bound for each nonzero element. If every generator power is nonzero, the same ring is a domain and then a DVR, without a Noetherian hypothesis. [Adic-completion DVR structures](../AdicCompletion/DiscreteValuationRing.lean) use this criterion.

[ResidueTensor](ResidueTensor.lean), imported as `Aglib.RingTheory.LocalRing.ResidueTensor`, gives closed-base-fibre Nakayama, surjectivity and finite-kernel injectivity tests over a local algebra. The original local structure-map, finite-module and quotient-flatness premises are explicit; no Noetherian assumption is introduced.

[ResidueFieldComap](ResidueFieldComap.lean): for a ring map `σ : A →+* B` and `t ∈ Spec B` over `s = σ⁻¹ t`, `Ideal.ResidueField.mapComap σ t : κ(s) →+* κ(t)` is `Ideal.ResidueField.map` over `σ`; the square `A → B → κ(t)`, `A → κ(s) → κ(t)` commutes (`Ideal.ResidueField.algebraMap_comp_eq_mapComap_comp`), and `κ(s) → κ(t)` is flat (`Ideal.ResidueField.flat_mapComap`). The fibre comparison of cohomology base change (`Cohomology/BaseChange/Modules/Composite`) consumes them.

[PrincipalMaximalIdeal](PrincipalMaximalIdeal.lean) is the lower native
principal-maximal-ideal provider used by the smooth-curve stalk constructions.
The geometric consumers keep their own field, smoothness and dimension inputs.

[EtaleLift](EtaleLift.lean) constructs finite etale algebras over any local ring
whose actual residue tensor products realize the supplied separable field
extension or etale residue algebra. Monic polynomial lifting, the resultant
unit criterion and native tensor-product comparisons give the construction;
Henselian, Noetherian and excellence assumptions are unnecessary.

[Finite projective-dimension bound](ResidueProjectiveDimensionBound.md) proves
`projectiveDimension M ≤ ringKrullDim R` for every finite module of finite
projective dimension over a commutative Noetherian local ring. The supplied
natural bound `n` witnesses finiteness; the conclusion bounds the actual
projective dimension, rather than every such witness `n`.

[CoefficientSection](CoefficientSection.md) constructs sections of the original
residue map in equal characteristic, including arbitrary imperfect residue
fields. [CohenRing](CohenRing.md) constructs a complete characteristic-zero DVR
with any prescribed prime-characteristic residue field and the original prime
as uniformizer. [CohenMap](CohenMap.md) lifts its actual residue point to an
injective local map into the original complete mixed-characteristic domain.

[ParameterIdeal](ParameterIdeal.md) constructs maximal-radical parameter sets
in Noetherian local rings. In a local domain of dimension at most two, any
prescribed nonzero nonunit extends to such a pair; its intermediate principal
quotient need not be regular or reduced. The
[completed parameter map](../AdicCompletion/CompleteParameterMap.md) preserves
these original maps and uses the residue and parameter equations to derive
finiteness.

[SquareZeroLift](SquareZeroLift.lean) treats a local `k`-algebra `A` with a `k`-algebra map
`ψ : A →ₐ[k] k` over a field `k`. Then `ker ψ = 𝔪` (`IsLocalRing.ker_algHom_eq_maximalIdeal`), and
`a ↦ [a - ψ a]` is a `k`-derivation `A → 𝔪/𝔪²` (`IsLocalRing.cotangentDerivation`). The
`k`-derivations into an `A`-module killed by `𝔪` are the `k`-linear maps on `𝔪/𝔪²`
(`IsLocalRing.derivationEquivCotangentSpace`). The lifts `A →ₐ[k] TrivSqZeroExt L M` of `ψ` are
`Hom_k(𝔪/𝔪², M)` (`IsLocalRing.trivSqZeroExtLiftEquiv`), naturally in `M`
(`IsLocalRing.map_comp_trivSqZeroExtLift`), and correspond to derivations
(`IsLocalRing.trivSqZeroExtLiftEquivDerivation`). For Noetherian `A`, `𝔪/𝔪²` is finite over `k`
(`IsLocalRing.finite_cotangentSpace_of_algHom`). The tangent space of a represented functor
([Picard/Tangent/Points](../../AlgebraicGeometry/Picard/Tangent/Points.lean)) consumes them.
