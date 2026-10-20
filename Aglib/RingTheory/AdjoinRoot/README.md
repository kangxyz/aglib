# Literal root-algebra base change

`BivariateTensor` constructs `AdjoinRoot.bivariateTensorEquiv` by the canonical
polynomial-tensor equivalence and Mathlib's root-algebra base change. The source
and target polynomial equality is supplied explicitly; no monicity, domain or
curve hypothesis is inferred. Root and coefficient formulas retain the literal
forward map. One implementation replaces the two identical source constructions.
