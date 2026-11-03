# Cohomology of the regular-point exceptional line

[ExceptionalPositive](ExceptionalPositive.lean) treats the actual full-point
blowup of an integral locally Noetherian regular scheme at a closed point
with two-dimensional stalk. It proves invertibility of the original
composite `O_X[0] → Rb_*O_X'[0] → Rb_*O(E)[0]`.
The second arrow is the derived image of the dual ideal inclusion,
normalized by evaluation at one. The residue field is unrestricted.

[OnePoleCanonical](OnePoleCanonical.lean) and
[OnePoleDerived](OnePoleDerived.lean) compare the same point-blowup one-pole
map with canonical and derived coefficients under their supplied original
projective normal-surface trace data, regular local base, normality,
dimension and coordinate hypotheses. They retain those comparison worlds
and the original exceptional-positive map; they do not assert a global
trace theorem for arbitrary models.

Present consumers include [OnePoleCanonical](OnePoleCanonical.md), [OnePoleDerived](OnePoleDerived.md).
