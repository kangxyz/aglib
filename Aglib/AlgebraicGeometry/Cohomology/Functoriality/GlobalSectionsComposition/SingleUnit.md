# Original global-sections composition on single units

`moduleDerivedGlobalSectionsPushforwardCompIso_singleUnit` pastes the
original native single units through the existing geometric derived
composition isomorphism. Its section comparison is the original
`modulePushforwardGlobalSectionsIso`, which is the identity on section
values. The proof uses the original complex-unit equation and Mathlib's
single-complex composition and natural-transformation formulas.

`moduleDerivedGlobalSectionsPushforwardCompIso_coefficientUnit` retains
an arbitrary actual coefficient arrow `M ⟶ g_*N`. It identifies the same
derived composite unit square with the literal original global-section
arrow. Global sections and module pushforward are not assumed exact.

`moduleDerivedGlobalSectionsPushforwardCompTriangleIso` transports the
original triangles through that same existing derived comparison. Its
shift compatibility follows from the original unit factorization. All
three inverse components are the original composition inverse, as recorded
by the component theorems. No second unit or replacement comparison is
constructed. The current consumer is the original Leray map comparison
in `Cohomology/Proper/DerivedStructure`.
