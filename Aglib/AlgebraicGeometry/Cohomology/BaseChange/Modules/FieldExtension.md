# Faithful field extension on original cohomology

Import `Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.FieldExtension`.

For a quasi-compact quasi-separated `f : X ⟶ Spec k`, an arbitrary field
homomorphism `σ : k →+* K`, a quasicoherent module sheaf `M` and every degree
`n`, `moduleCohomologyFieldBaseChangeEquiv` is the actual canonical map
`K ⊗[k] Hⁿ(X,M) ≃ₗ[K] Hⁿ(X_K,M_K)`. Its source and target carry their
original structural actions. The scheme is the literal native pullback and
the coefficient uses its original first projection.

The unit pure-tensor equation identifies the forward map with geometric
cohomology pullback. Faithful tensor extension then proves
`subsingleton_moduleCohomology_iff_fieldBaseChange`, and
`moduleCohomology_finrank_fieldBaseChange` gives equality of dimensions over
the respective fields. These results require neither Noetherianity,
properness, finite presentation nor finite-dimensional cohomology. As usual,
native `finrank` is zero in infinite dimension; the underlying linear
equivalence and vanishing reflection do not rely on that convention.

The geometric comparison is the existing canonical qcqs flat base-change
theorem in [Qcqs](Qcqs.lean). Faithfulness follows because a nonzero vector
space over a field is faithfully flat. The actual-fibre H⁰ neighbourhood
consumer belongs to
[Proper/H0Vanishing/FieldExtension](../../Proper/H0Vanishing/FieldExtension.md).
