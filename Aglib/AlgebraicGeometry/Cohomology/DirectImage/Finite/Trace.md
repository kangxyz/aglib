# Finite trace coordinates on original cohomology

For the actual finite diagram `Y → X` over a finite faithful local algebra
`A → B`, assume the original maps `X → Spec A` and `Y → Spec B` identify
their function fields and `X` has normal stalks. The theorem
`finiteTraceCohomology_length_le` proves, in every degree `q`,

```text
length_B H^q(Y,O_Y)
  ≤ length_B H^q(Y,O_Y)[image(d)] · length_κ(A) κ(B)
      + r · length_A H^q(X,O_X).
```

Here `r` and `d` are the original function-field degree and trace-lattice
discriminant, fixed by `A → B` before choosing the diagram. Normality of
`A` is retained for its original valued trace lattice. All lengths lie
in `ℕ∞`; no finiteness, freeness of the finite morphism or splitting is
assumed. The trace-coordinate cohomology map is only A-linear. Restriction
of the original B-action accounts for the actual residue degree.

The arrows are the original trace-coordinate and adjugate sheaf maps.
The scalar factorization is transported through the native affine
cohomology comparison. The original structural square proves the scalar
tower on the unchanged `Sheaf.H` group, and the native finite-biproduct
comparison supplies the final target length. No trace or scalar
compatibility condition is added as an input.

The current application is the uniform separable surface H1 bound. This
module proves its actual-diagram length step. The dominating-model
construction, nonzero discriminant from separability and uniform
scalar-torsion bounds remain separate inputs to that further theorem.
