# Presentations of the original finite pure degree-p DVR extension

[Monogenic.lean](Monogenic.lean) constructs a presentation of the original
finite pure degree-p DVR extension using the companion
[FiniteDegree](FiniteDegree.md) results.

The main generic statement starts with actual DVRs A and B, a finite
torsion-free original A-algebra B, compatible actual fraction fields K and L,
and a finite purely inseparable extension L/K with `finrank K L = p`,
`Fact p.Prime`, and `CharP K p`. It constructs a, z, and

```text
h : IsAdjoinRootMonic B (X^p - C a)
algebraMap A B a = z^p
h.root = z
h.map = Polynomial.aeval z.
```

No monogenicity, power basis, ramification equality, or defectless condition
is supplied to the main theorem.

In residue degree one, the residue map κ(A) → κ(B) is surjective. Repeated
division by any actual B-uniformizer τ gives, for each n,

```text
b = q(τ) + τ^n c,  q ∈ A[X], c ∈ B.
```

The previous leaf gives `τ^p = algebraMap A B a`; a belongs to the maximal
ideal of A. Taking n=p makes B/A[τ] equal its multiple by that maximal ideal.
Nakayama applies because B is finite over A and gives A[τ]=B.

In the other case the actual extended maximal ideal equals the maximal ideal
of B. Prime residue degree supplies a residue class outside the image of
κ(A), and any original lift z generates the residue field. Lift its polynomial
coefficients through A → κ(A). This gives `B=A[z]+πB` for an actual source
uniformizer π, and Nakayama again proves A[z]=B.

For either root, use the native minimal-polynomial presentation of the given
B. Its power-basis rank shows `natDegree(minpoly A z)=p`. The original equation
`z^p=a` makes this minimal polynomial divide `X^p-C a`; monicity and equal
degree identify them. The resulting map is literally `aeval z`. Consequently
`h.powerBasis` and `h.basis` are the original power bases, with generator z,
dimension p, and basis entries `z^i`; they are outputs, not inputs.

The literal-normalization specialization takes
`Module.Finite A (integralClosure A L)`. Its DVR, fraction-field, and
torsion-free structures are derived from the existing original-normalization
supplier. Ring Noetherianity is not substituted for this module-finiteness
hypothesis. No complete, henselian, separable-residue, perfect-field, smoothness,
or finite-p-rank assumption is used.

The reviewed mathematics also gives that a is a uniformizer in the first
case and a unit with non-pth-power residue in the second. Those extra
coefficient-classification corollaries are not yet separately exposed in the
Lean module. They are not premises of its presentation or of the existing
ring differential trace consumer.
