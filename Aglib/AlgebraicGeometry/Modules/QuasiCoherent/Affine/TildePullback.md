# Native tilde pullback composition

Source: [TildePullback.lean](TildePullback.lean).

The existing bundled-arrow natural and component composition laws retain their
original constructors, statements and implementations. The provider is unchanged
from the pre-integration main branch.

Additional literal-ring-map natural and component formulas live in
[TildePullback/Composition](TildePullback/Composition.md). Consumers requiring
those formulas import that focused leaf directly.
