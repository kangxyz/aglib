# The native change representing the original pointed isomorphism

The theorem identifies the actual supplied scheme isomorphism. For any field k,
literal Weierstrass equations W,V and an actual `E : curveOver V ≅ curveOver W`
sending V's original infinity section to W's original infinity section, it
constructs an actual native change C and a proof `hC : C • W = V` such that

```lean
E = eqToIso (congrArg curveOver hC.symm) ≪≫ VariableChange.projectiveOverIso W C
```

`variableChangeOverIso` is precisely this typed coefficient-cast composite.
Its structural and infinity equations are explicit. The statement needs
no nonzero discriminant premise: the existing affine classification and the
native integrality/separatedness of these literal field cubics suffice.
No group law, perfectness, characteristic restriction, chosen C or desired
isomorphism premise is added.

The existing `PointedIsomorphism` supplier already proves triangular affine
coordinate formulas by principal-ideal colength. Its single classification
body now exports `affineAlgEquiv_exists_variableChange_with_coordinates`,
retaining the same chosen C, coefficient identity and both actual coordinate
images; the old coefficient-only theorem is its thin consequence. There is
no repeated proof of pole flags, triangularity or the classification calculation.

The new comparison proves that the unchanged homogeneous Z chart of the
native Proj map restricts to the existing `VariableChange.affineMap` for the
same C. It reuses the native localization-map square and the original
homogeneous coordinate formulas. For E in the displayed direction, the
existing affine equivalence of E.symm is exactly the direct pullback
A_W→A_V. Its retained coordinate equations identify it with that affineMap.
Equality on the actual dense affine chart and relative separatedness then
identify E itself with the canonical projective Over-isomorphism.

Original basis: HEAD `3a4d549981ced306d89d3ed55418c9e6a25f86c4` with its live
overlay. The minimal supplier refactor starts from selectively adopted
published PointedIsomorphism source
`c4e27ffface9d767f8d3348c823da299789a80945c4fde8dac4dd17715166586`;
its old public statements, simp registrations and published Spec.map coercion
correction are preserved. The native projective-change provider remains
unchanged at `c2be14ed25310cb3caa3e33aedcfede7cb15577478a84f6e07b665e15e2b3755`.
The adopted source/guide and adoption record are retained separately. No
old native result is assigned to this changed pair or its new interface.
The completed raw genus-one presentation and its providers remain immutable.

The lower interface has its genuine own native pass at
`5dd444494002ad4762cf88c280cd28ff66acd0f0e9c949d27c23127d75bafab0`,
in `remote-e88eb7d69a10450791de9b57fb693946`, SOURCE
`01ba21339e8262b1d7da0963b031afbbcc781decf650917e5e2a65855651d8b2`.
The complete exact-map consumer has its own native pass at Lean source
`2d4d9db30903724a8891bfac154522f5e24f516b3c1a2738630ace56774a656d`,
in `remote-9759426272e94d978258f22c9f53048d`, SOURCE
`2edb1db3c53113cc7f0fb9bde0d59c97e772b0210dc9488e8e3c83a4613eb368`.
It passed in 26 seconds at the default 200000-heartbeat budget. The shared
graph failed only on independent `FromSections.LineSource` and
`FromSections.FieldSpan` leaves; those failures do not change this leaf's
native result. The lower and upper Lean sources remain unchanged, and their
passed source/guide snapshots are preserved separately from this doc-only
status correction. Native success does not replace independent mathematical
review.

The exact scope is recovery of the supplied pointed isomorphism over its
original field. It does not assert regularity of models, resolution,
contraction, or invariance of minimum equations under etale base change.
