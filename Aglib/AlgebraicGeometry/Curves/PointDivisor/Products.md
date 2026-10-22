# Products of original point-pole sections

[Products.lean](Products.lean) retains the actual smooth proper
geometrically connected genus-one curve over its arbitrary original field,
its original rational point, and the normalized divisor-sheaf comparison
from [PoleFunctions](PoleFunctions.lean).

`tensorPowerAddIso` uses the native tensor unit and associator, together
with the explicit natural-number addition transports. `poleTensorAddIso`
specializes those actual maps to the original positive point module.
No graded-algebra compatibility or family of frames is an input.

The sheaf-map comparison is proved by induction on the first pole bound,
keeping the line bundle and its given point-divisor isomorphism abstract.
The zero bound uses the original unit map and the zero-power rational
value formula. A successor bound uses the original associator and native
divisor multiplication. The proof tests pure section tensors on each open
through the native sheafification extensionality theorem. Nonempty opens
are detected by the actual rational-value equivalence; on the empty open,
the existing divisor-sheaf section module is a subsingleton. This proves
the actual sheaf-map diagram before evaluating global sections.

`sectionsToFunctionField_tensor` identifies the original native tensor
product with literal multiplication in the same original function field,
for all natural bounds including zero. Its section maps are the already
normalized `sectionsToFunctionField`; their field action is the actual
`functionFieldConstants` map of the original structural morphism. Thus
this product uses the original scalars and original sections, without a
chosen vector-space replacement or additional scalar-tower premise.

The integral, Noetherian and closed-point DVR structures required by the
native fractional objects follow from the given curve properties, using
the producers stated in PoleFunctions. No characteristic, algebraic
closure, norm, group-law or Picard-representability hypothesis is added.
Native evidence is bound to the exact source and run reported by the
author; this guide alone does not assert that a pending source passed.
