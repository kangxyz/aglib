# The original finite projective embedding

[Embedding.lean](Embedding.lean) constructs
`Scheme.Blowup.ProjectivePresentation.exists_projective_embedding B f j`.
The inputs are an original blowup datum over a locally Noetherian scheme X,
an arbitrary map f from W to X, and an actual finite closed embedding of W
over an affine base Spec A. The output is an actual finite closed embedding
of the literal fibre product of B with f, retaining its original map to
Spec A through W and j.

The proof chooses the existing common negative-twist epimorphism. The
compatible affine frame cover and the canonical restriction comparison
retain that same original row. Its local finite-family map is identified
with the scalar Rees polynomial embedding by `ChartCoordinates`.
The native restriction proposition is converted to its literal row equation
over abstract module objects, using separately proved original-row and
local-family value equations. The same local line, family and epimorphism
proof are retained through the finite-family map comparison.
The complete restriction comparison and its base triangle are proved with
an abstract coefficient ring before specializing to the chosen affine cover.
Coefficient naturality identifies the local target with the actual
projective base-change square. These squares prove that the original
relative coordinate graph is closed. Composing it with the original base
embedding and Segre supplies the requested finite projective embedding.

The raw coordinate map to projective space over A is not used as a closed
map. The closed map is its relative graph over W. No projectivity of X,
flatness of f, global generators of the original ideal, or comparison with
the blowup of its nonflat image ideal is assumed.

This single-step construction is the projectivity supplier for the actual
pulled point-blowup chain in the proper-surface contraction route. The
chain induction, supplied domination map, comparison graph, and contraction
arguments remain distinct consumers.
