# Purely inseparable rational-function extensions

[RationalEvaluation](RationalEvaluation.lean) constructs the actual rational evaluation map after an
algebraic extension of constants and proves its compatibility with the supplied
original rational-function map.

[RationalFunction](RationalFunction.lean) uses the native relative perfect closure of a field inside
its algebraic closure. Over separably closed constants, their algebraic closure
embeds into this perfect field, giving an algebraic rational-function extension
over algebraically closed constants. The original field inclusion is purely
inseparable, without a finite-degree restriction or a tensor-domain assumption.

The public
`Field.exists_ratFuncAlgebra_perfectFunctionField` theorem constructs an actual
rational-function algebra on `Field.perfectFunctionField E`, proves algebraicity,
and retains the equality with the supplied original rational-function map.
No extra constant-action or tower premise is required from the caller.

The separate [geometric purely inseparable comparison](../../AlgebraicGeometry/EtaleCohomology/Fields/PurelyInseparable/README.md) transports
original prime-to-characteristic root cohomology; no multiplicative-sheaf
invariance is claimed here.

## Finite constants in a supplied rational extension

[FiniteConstantRoots](FiniteConstantRoots.md) supplies the distinct
`IsPurelyInseparable.exists_finite_constant_field` theorem. The original
image of its field `F` has supplied rational presentations in a
transcendental `t` over `K` inside an algebraically closed ambient field.
For a finite purely inseparable `L/F` in that same ambient field, it
constructs a finite purely inseparable constant field `E/K` and a
characteristic-power root
`z` of the original variable. The element `z` is transcendental over `E`,
and the original extension image lies in the literal field `E(z)`.
The rational presentation and original coefficient maps are explicit;
no bound on the imperfection degree of `K` is used.

[Nagata.Polynomial](../../RingTheory/Nagata/Polynomial.md) uses this finite
constant-root theorem. The perfect rational-function construction in
[RationalFunction](RationalFunction.lean) remains a separate interface
with its original hypotheses and declaration names.

[NonPowerComplement](NonPowerComplement.md) constructs, for a field of prime
characteristic and an element outside its Frobenius image, an actual maximal
subfield avoiding that element and containing the image. The extension has
degree `p`, with the original element as monogenic root and the basis of its
powers. Infinite ambient p-rank is allowed. The coefficient-expansion and
pure degree-p differential-trace consumers retain this original inclusion.
