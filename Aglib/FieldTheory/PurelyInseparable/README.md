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
