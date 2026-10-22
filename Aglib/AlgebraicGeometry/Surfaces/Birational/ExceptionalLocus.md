# Actual contracted curves and their finite count

The maintained set contractedCurves f consists of actual native
IrreducibleCloseds X with carrier dimension exactly one and subsingleton
original image f''C. contractedCurveCount f is Nat.card of that literal
subtype. Its use as a finite count is guarded by a proved finiteness theorem;
zero does not silently use the infinite-subtype convention of Nat.card.

The finiteness theorem starts with integral X and Y, Noetherian X,
locally Noetherian normal actual stalks of Y, proper dominant original f,
its actual functionFieldMap-isIso, and dim X≤2. It needs no dimension bound
or global Noetherianity on Y. An actual contracted curve misses the original
target isomorphism locus, since otherwise original restriction injectivity
would make the entire curve a singleton. Its original generic point has
coheight one: dimension one excludes a closed generic point, dim X≤2 gives
coheight≤1, and the nonempty generic isomorphism locus excludes coheight0.
Noetherian finiteness of coheight-one points on the proper closed source
complement proves finiteness, using the native original generic-point
bijection with irreducible closed subsets.

With dim Y≤2 as well, empty contracted-curve set implies the original f is
an isomorphism. Every bad target point is closed. A nonclosed source point
in its fibre would have a proper one-dimensional closure, which is an
actual contracted curve. Thus every fibre over a bad point consists of
closed points; Noetherian sobriety makes that closed fibre finite. The
original proper birational finite-fibre criterion and target locality give
IsIso f. The zero-count version first invokes the actual finiteness proof.

Original postcomposition gives an actual inclusion of contracted-curve
sets. The cardinal monotonicity and strict-witness lemma retain explicit
finiteness of the composite set; geometric callers discharge it using the
proved finite_contractedCurves theorem.

The strict-decrease producer constructs an actual curve. For an original
closed integral dimension-one divisor j:D→B missing the ambient generic
point, lift j(η_D) through the actual codimension-one isomorphism open of
g:X→B and close that original source point. Proper closedness gives
EXACTLY g''C=range j. This excludes contraction by g and, when the original
postmap contracts D, proves contraction by the composite. The curve is
not assumed globally isomorphic to D.

contractedCurveCount_lt_pointBlowup specializes to the ACTUAL datum
B=blowupDatum((Y.fromSpecResidueField y).ker). Its inputs are integral
Noetherian X of dimension≤2, integral locally Noetherian Y with regular
actual stalks and dimension≤2, original closed y with local dimension2,
and original proper dominant g:X→B.Y with its actual function-field map
invertible. The integral blowup instance in the latter premise is derived
from the original point, not an extra hypothesis. Target blowup normality,
local Noetherianity and dimension are derived from the actual point APIs.
The literal exceptional residue fibre is integral of dimension one via
the passed comparison with P1 over the SAME original residue field.
The original projection equations show that the original blowdown
contracts it. Finiteness of the composite curve set is proved in the
same theorem before using strict cardinal comparison. No contracted
component, global curve/divisor isomorphism, desired strict decrease,
factorization or detector is an input.

The regular-point fibre comparison supplies the exceptional projective line.
The theorem does not construct a regular model from singular initial data.
