# Case-II child generators before the child cone

API: [exists_generators_at_closed_singular_point](CaseTwoChildGenerators.lean#L91), [exists_original_generators](CaseTwoChildGenerators.lean#L126).

`CaseTwoChildGenerators.lean` derives three genuine maximal-ideal generators
on the original closed singular child stalk before assuming any child rank,
Hilbert function or tangent kernel. The input is the parent's actual generating
triple, full normalized square kernel and a genuine cubic relation. No parent
normality, rationality, Gorensteinness or dimension hypothesis is added.

The private parameter-chart proof uses the actual child prime and its original
polynomial lift. `prime_span` and the native local triple give the generators;
the existing stalk equivalence transports them back to the original scheme
stalk. Its actual localization dimension gives dimension two. The unique
shared ThreeGenerators theorem then derives cotangent rank three.

The public local-spectrum theorem uses the existing two-chart cover, the same
cubic's native swap and the existing full-kernel coordinate law. Its first
generator is the image of the corresponding original denominator, either t
or s. No child coefficient field is chosen.

`exists_original_generators` is the thin arbitrary-scheme consumer through
PointLocalization. It retains the literal original pointLocalRingMap and the
same denominator alternatives on the original child stalk. Genuine local
Noetherianity is transported from the actual local-spectrum blowup.

The later rational exceptional-Hilbert theorem may consume this derived rank
and independently established child rationality/normality. That later Hilbert
function, child classification, markings and termination are not asserted here.

The parent coefficient ring is a commutative Noetherian local domain.
The displayed child generators and full kernels are on the original child
stalk and use its original residue field.

Present consumers: [OriginalPathCones](OriginalPathCones.md).
