# Original generic points and actual stalk dimension

`GenericPoint.lean` owns original generic-point facts for integral schemes.
`Scheme.fromSpecStalk_bot` sends the zero prime of an actual stalk to the
original generic point under that stalk's native spectrum map. Its original
implementation and hypotheses are unchanged.

`Scheme.ne_genericPoint_of_stalk_dimension_two` says that an original stalk
of dimension two cannot lie at the generic point. The native function field
is exactly that generic stalk, and its Krull dimension is zero. The theorem
requires only integrality and the stated stalk dimension; it does not add
closedness, regularity, Noetherianity, a ground field, or a selected field model.

The complete dimension-two producer is moved once, byte-for-byte, from
`Surfaces/Birational/Factorization.lean`. Its public name and header are
preserved; that former owner imports this lower leaf and retains every later
proof unchanged. Native Krull-dimension-of-field and NormNum imports support
the same proof without an upper surface dependency.

The complete changed lower owner `8697714e` passed its normal native check
(`reupload-own-198`) in 2.1 s leaf / 4.5663 s total, exit 0, no aggregate guard,
and a terminated owned process group. This includes both original laws.
The changed original Factorization consumer remains unaccepted: its separate
no-build readiness check found 29 dependency-gap roots and performed no proof
compilation. No upper acceptance or factorization conclusion is transferred
from the lower pass. The geometric use is to derive a genuinely nonempty
centre complement and original point-blowup integrality for subsequent
unit-square gluing; this file constructs no cover, alternative blowup, or
global one-pole map.
