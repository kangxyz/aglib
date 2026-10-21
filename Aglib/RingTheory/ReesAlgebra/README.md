# The actual native Rees algebra and its grading

[Grading](Grading.lean), in `reesAlgebra`, grades the existing Mathlib subalgebra
`reesAlgebra I` inside A[t]. Its degree-n component contains exactly the actual
polynomials supported at n; the original coefficient lies in I^n. Coefficient
extraction proves the internal direct sum and identifies the actual homogeneous
projection with the corresponding monomial.

`degreeZeroEquiv` identifies degree zero with the original ring A by constant
coefficient. Its inverse has the same image in the Rees algebra as the original
structural `algebraMap A (reesAlgebra I)`. These results work over arbitrary
commutative rings and ideals, including zero and unit ideals. No domain,
Noetherianity or nontriviality hypothesis is imposed.

[Away](Away.lean) constructs the canonical A-algebra equivalence between the
actual homogeneous localization at a*t and the existing
[saturated subalgebra A[I/a]](../Localization/Away/SaturatedChart.lean). Evaluation
at t=1 gives the actual map into A[1/a]; the localization zero criterion proves
injectivity, and ideal-power induction identifies its exact image. The original
degree-zero scalar map, b/a and general homogeneous-fraction formulas are
proved. The argument covers zero and nilpotent a as well as zero/unit ideals,
without a domain assumption.

The next geometric steps are the actual Proj chart and overlap identifications,
Cartierness of the actual image ideal, universal lift/gluing, and global/flat
compatibility. These ring comparisons do not supply the general
[blowup](../../AlgebraicGeometry/Blowup/README.md) existence, atlas, properness or
flat-base-change families.

[GradedTransitionGenerators](GradedTransitionGenerators.lean) constructs actual
submodules of an internally graded module from componentwise homogeneous-action
closure. It proves that every finitely generated homogeneous submodule is
spanned by homogeneous vectors in bounded degrees, by decomposing a finite
ordinary generating set. No finiteness of individual components is assumed.

[GradedTransition](GradedTransition.lean) applies this to a finite module over
the native Rees algebra with degree-lowering maps. Its interface keeps both
shift naturality and the formula that lowering homogeneous multiplication back
to its source degree is the original scalar action. Over a Noetherian base it
provides one shift bounding the degree-zero image by the ideal power and killing
the degree-zero kernel under the shifted transition. The kernel is an actual
homogeneous Rees submodule; transitions are not assumed injective or surjective.
This is the algebraic input to formal functions, not a geometric finiteness
supplier or an unconditional formal-functions theorem.

`ModuleImage.lean` identifies the range of the original scalar-extension map
`reesAlgebra I ⊗[A] M → PolynomialModule A M` with the native adic-filtration
Rees submodule. Its proof works for arbitrary modules, including nonflat
modules, and does not identify the tensor source with its image.
The transition estimates follow the graded-module argument of
[Stacks Project, Tag 02OA](https://stacks.math.columbia.edu/tag/02OA), retaining
both action compatibilities in the formal interface.
