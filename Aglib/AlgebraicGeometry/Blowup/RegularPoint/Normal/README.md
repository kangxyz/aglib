# Centre-ideal frames and normal lines

[Frames](Frames.lean) constructs the original centre ideal line, its
conormal restriction and dual normal restriction on the native blowup.
For `I=(a,b)` with `a` regular and `b` regular modulo `a`, it uses the
actual saturated denominator frame. The regular-local dimension-two
specialization keeps the original residue-field projective line and
normal/conormal maps.

[Sections](Sections.lean) computes restriction and Laurent coefficients
in those original frames. Its two-chart results retain the regular-pair
conditions in both orders.

[TwistedLine](TwistedLine.lean) defines the pullback of a supplied line
tensored with the dual centre ideal on the same blowup. This construction
works for an arbitrary commutative ring and ideal; it requires no
regularity, domain or Noetherian hypothesis.
The one-pole differential and exceptional-positive cohomology maps use
these lines and frames.

Present consumers include [Relative forms on saturated regular-pair charts](../../Differentials/RegularPair/README.md), [Universal blowups and saturated affine charts](../../README.md).
