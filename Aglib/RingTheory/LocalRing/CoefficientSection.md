# Actual coefficient sections of complete local rings

Let F be the specified coefficient field and let R be a commutative local
F-algebra. Write `k = IsLocalRing.ResidueField R` and `m = maximalIdeal R`.
Assume `Algebra.FormallySmooth F k`. The construction retains the original
F-action on R and its induced action on the literal quotient k.

`residueCompletionSection` is the native formally smooth lift of the
identity `k → k` into the actual completion `AdicCompletion m R`.
`evalOne_comp_residueCompletionSection` identifies its first projection
with that identity. The finite-order maps are explicit:

```text
coefficientSectionMod n : k →ₐ[F] R / m^n.
```

They are the actual completion projections of the chosen lift.
`coefficientSectionMod_compatible` gives compatibility with the native
ideal-power quotient maps, including order zero.

When R is complete for its maximal ideal, `coefficientSection` composes
that lift with the inverse of the canonical completion equivalence. Its
quotients are exactly `coefficientSectionMod n`, by
`mk_comp_coefficientSection`. The residue equation is

```text
residue R (coefficientSection F R x) = x.
```

`residue_comp_coefficientSection` gives the same equality as an equality
of F-algebra maps. `coefficientSection_algebraMap` retains the original
coefficient equation, and `coefficientSection_injective` proves that the
constructed section is an embedding. The existential endpoint is
`exists_coefficientSection_of_formallySmooth`.

No Noetherianity, domain, finite-type, finite transcendence-degree, or
perfect-residue hypothesis is used in this conditional construction. The
formal-smoothness premise remains explicit; a coefficient section is never
assumed.

For residue characteristic zero, `ratAlgebraOfResidueCharZero` derives an
actual ℚ-action on R. Every proper quotient of R maps to its actual residue
field and consequently has characteristic zero. The native
`EqualCharZero.nonempty_algebraRat_iff` then constructs the rational action.
The actual residue field is formally smooth over ℚ by
[`Algebra.FormallySmooth.field_of_perfectField`](../Smooth/Field.lean),
whose finite-support cotangent argument imposes no finite-generation
assumption on the extension.

`coefficientSectionOfResidueCharZero` is the resulting actual ring section.
`residue_coefficientSectionOfResidueCharZero` and
`exists_coefficientSection_of_residue_charZero` record the original residue
identity. This corollary assumes only a commutative local R, maximal-adic
completeness, and characteristic zero of its actual residue field.

The implementation reuses
`Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq` from
`Mathlib/RingTheory/Smooth/AdicCompletion.lean`. That existing theorem
already constructs compatible quotient lifts internally. This is an
additive native-inventory correction to the fixed R.F2 research packet;
the packet is unchanged, and its lift induction is not duplicated here.

For a prime p and `CharP R p`, `coefficientSectionOfCharP` installs the
native `ZMod p` action and applies the same arbitrary-field smoothness
theorem. `residue_coefficientSectionOfCharP` and
`exists_coefficientSection_of_charP` retain the literal residue identity.
The residue field may be imperfect and have infinite p-rank. This is an
equal-characteristic statement and does not put a field of characteristic p
inside a mixed-characteristic ring.

The mixed-characteristic Cohen coefficient existence problem remains
separate: arbitrary-residue Cohen-ring enlargement and compatible lifting
of its finite p-power quotients into the given complete local ring are not
constructed here. Nor does this leaf establish the final finite
regular-subring conclusion of R.F2.

Source basis: Aglib HEAD `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Lean 4.34.1, and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
