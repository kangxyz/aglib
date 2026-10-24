# Length from a scalar factorization

For original linear maps `f : M →ₗ[R] N` and `g : N →ₗ[R] M` with
`g.comp f = d • id`, the theorem
`Module.length_le_torsionBy_add_of_comp_smul_id` proves

```text
length_R M ≤ length_R M[d] + length_R N.
```

The proof puts the actual kernel of `f` into the original `d`-torsion,
uses the exact kernel/range sequence, and puts the actual range into `N`.
No splitting, finite-length hypothesis, or chosen replacement module is
required. The inequality is valid for lengths in `ℕ∞`.

For a local ring map `A → B`, with the original compatible actions on a
B-module `M`, `length_le_torsionBy_mul_residue_add_of_comp_smul_id` gives

```text
length_B M ≤ length_B M[image(d)] · length_κ(A) κ(B) + length_A N.
```

The two maps need only be A-linear. The proof identifies the original
A-torsion with the restriction of the original B-torsion, then applies
native local-ring length restriction. No B-linearity of the trace-coordinate
map is assumed. The residue degree is retained; no rational or separable
residue-field hypothesis occurs.

The current consumer is the finite separable surface bound. Its original
trace-coordinate and adjugate sheaf maps induce precisely such linear maps
on cohomology. This lemma performs the length step after those geometric
maps and their scalar normalization have been proved. It supplies neither
the finite-domination diagram nor the original trace/conductor identity.
