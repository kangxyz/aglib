# Scalar kernels, cokernels and exactness

[Basic](Basic.lean), imported as `Aglib.RingTheory.ScalarHomology.Basic`, defines `Module.ScalarKernel`, `ScalarCokernel`, `scalarKernelMap` and `scalarCokernelMap` for actual scalar multiplication on arbitrary modules over a commutative ring. Ring and module universes may differ. `principalConnecting` and its exactness lemmas give the actual six-term scalar-homology sequence from an injective/exact/surjective module sequence. No finite-length premise is required for these maps or exactness.

`scalarKernelEquiv` and `scalarCokernelEquiv` transport the actual homology through compatible module equivalences. [BaseChange](BaseChange.lean) gives `scalarKernelBaseChangeEquiv` under flat scalar extension; `principalCokernelBaseChangeEquiv` requires only the commutative scalar rings and algebra structure, on an arbitrary coefficient module. Restriction equivalences require both module actions and their `IsScalarTower`.

[Principal Euler](../Multiplicity/PrincipalEuler/README.md) consumes these maps after supplying finite scalar lengths where integer Euler identities need them. Its localization leaf imports the lower base-change interface directly and has no interchange/associativity dependency. The lower cokernel construction retains its exact source ranges without importing the original principal-face application.
