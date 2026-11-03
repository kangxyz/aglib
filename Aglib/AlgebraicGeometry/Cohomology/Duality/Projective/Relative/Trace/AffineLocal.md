# Original affine comparisons for the relative projective trace

[AffineLocal.lean](AffineLocal.lean) contains the original affine-model and
restriction constructions used by [Core](Core.lean). The public trace
interfaces remain in `AlgebraicGeometry.Scheme.Cohomology` and are reexported
through Core. This factorization introduces no new trace or sheaf model.

`relativeProjectiveAffineHigherIso` is the original higher-image comparison
on an actual affine open chart. `relativeAffineHigherNatIso` and its
`_original` equation retain the original restriction comparison followed by
the whiskered affine-model comparison. The component equation connects these
same maps without replacing their source or target objects.

`affineRelativeTraceHom` retains the original affine trace. Its naturality
and identity equations concern the actual scheme maps and structural scalar
maps. `relativeAffineTraceLocal` composes this trace with the original
higher restriction comparison; its factorization, sections, naturality,
refinement and congruence equations are the inputs to global gluing.

The coefficients remain arbitrary quasicoherent module sheaves in the
original projective pullback square. The finite projective-coordinate
indexing and degree inputs are retained by each theorem. These local
comparisons do not assert faithfulness of global sections, introduce a
proper exceptional inverse image, or provide a surface-resolution theorem.
Core proves the original global trace and its comparison laws under its
stated separated-base hypotheses.
