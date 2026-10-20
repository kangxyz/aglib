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
