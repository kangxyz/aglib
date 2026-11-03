# Native coinduction of the differential trace

Source: [Coinduction.lean](Coinduction.lean).

For the same normal Noetherian A, fraction field K, finite pure degree-p L,
finite normalization B, and finite raw exterior module M as IntegralClosure,
`integralClosureTraceCoinduced` makes the constructed transpose B-linear into
Mathlib's native coextension along the original map A → B. The target is
Hom_A(B, M**), with action (bφ)(c) = φ(cb); M** receives no B-action.

The coefficient base Λ and A lie in `Type u`, while the specified fraction
field K and extension L retain independent universes `Type v` and `Type w`.
The normalization B and its raw forms remain in `Type w`; M and M** remain in
`Type u`. Native coextension has carrier universe `max w u`. The helper
`originalFunctionalOnRestriction` independently sizes A, B, and the coefficient
module, retaining their literal original carriers and actions. No universe lift
or replacement field/module is introduced.

The evaluation theorem recovers the original transpose literally. The generic
formula is the original differential trace on bω. This leaf imports only the
algebraic trace and native change-of-rings API, not geometric duality or a
Hom-complex coefficient model. A later coefficient identification must use
its actual A-linear isomorphism and native coextension functor.

Proof: curry multiplication followed by the raw trace. Additivity is that of
the raw trace; B-linearity is associativity of the original B-action on raw
forms. The native coextension equivalence transports these equations without
changing their values. No separability or ordinary field trace enters.

This implementation is adapted from the historical IntegralTraceCoinduction
candidate, with its unnecessary higher homological import removed.

`integralClosureTraceCoinducedOfBasis` uses a supplied actual isomorphism
Θ : A ≃ₗ[A] M, followed by native bidual evaluation, to normalize the target
to native coinduction of A. Its evaluation theorem explicitly recovers
`eval (Θ (normalized_value)) = original_transpose_value`. There is no
second orientation and no suppression of the bidual coefficient map.

## Same fixed scalar after normalization

`integralClosureTraceCoinducedOfBasis_smul_mem_range` takes the already supplied
image bound for the original transpose: every A-linear functional B → M**,
after multiplication by the fixed s : A, lies in its image. For the same actual
Θ and normalized coinduced map, it proves that every native coinduced coefficient
after multiplication by `algebraMap A B s` lies in the normalized image. It does
not choose another scalar; nonzeroness is retained separately by the caller.

The proof reads the same native functional on the original algebra-module B,
using the two original scalar-action formulas, and composes it with Θ followed
by bidual evaluation. A preimage supplied by the transpose bound is also the
normalized preimage, as shown by the existing evaluation law and native
coinduction's right-multiplication action. No B-action on A or M** is added.

This algebra supplier is independent of sheaf restriction and trace gluing.
The geometric consumer must still construct JY and prove the original whole
identity `tauY.comp JY = integralClosureTraceCoinducedOfBasis ...`; only then
does the same scalar meet the existing canonical-trace H1-annihilation input.
