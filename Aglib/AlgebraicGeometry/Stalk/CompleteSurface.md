# Normal completion of an original closed surface stalk

Import `Aglib.AlgebraicGeometry.Stalk.CompleteSurface`.

`Scheme.Hom.normalDomain_completion_stalk_of_complete_surface` takes a
complete local domain `A` of dimension two, an integral scheme `X`, an
actual proper dominant `f : X -> Spec A`, and an original globally closed
point `x`. Its original stalk must be integrally closed, dimension two and
genuinely Nagata. The conclusion is that the literal maximal-adic completion
of this same stalk is a domain and integrally closed.

There is no birationality, global dimension bound, global normality of `X`,
Noetherianity or normality premise on `A`. Noetherianity of the stalk follows
from its Nagata property, and its domain property follows from integrality
of `X`. Neither finiteness over `A` nor completeness of the stalk is assumed.

The original proper map sends `x` to the actual closed point of `Spec A`.
Dominance and the original function-field/stalk equation prove injection of
the original stalk scalar map. Its native closed-base residue comparison
transports the derived finite original residue map across the SAME residue
equivalence. The existing ring-theoretic normal-completion theorem then
applies to that actual scalar action.

The intermediate-field completed-branch consumer delegates this proof once,
retaining its own completeness, closedness, dimension and Nagata discharge.
The theorem itself does not assume or construct a resolution or point chain.
