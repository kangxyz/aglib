# Finite normalization of a rational adjunction

The module treats a normal Nagata domain `R` of Krull dimension at most two,
its supplied fraction field `K`, and the literal subalgebra `S = R[x]` inside
`K`. All tested fields remain in `Type u`, with auxiliary test universe zero.

The local branch first assumes the nonzero adjoined element belongs to the
selected maximal ideal. Associated primes of its generator quotient are
pulled back through the actual localized-module map. The lower module
identifies their local rings with coefficient DVRs. Their quotients are
localizations of quotients of the original Nagata ring and have dimension
at most one. Nagata-AU1, the associated-DVR criterion and AU2-to-N1 give
finite literal local normalization under `atPrimeFractionMap S K m`.

For a general maximal ideal, the actual residue field supplies a polynomial
relation with leading coefficient outside its contraction. Inverting that
one coefficient makes the relation monic and leaves the selected local ring
unchanged. Set `u = f(x)` and use the actual finite birational inclusion
`R[u]` into `R[x]` in the same `K`. If `u` is zero, finite Nagata ascent
handles the local ring. Otherwise the preceding local branch applies to
`R[u]` at the contracted maximal ideal.

`finite_atPrime_of_finite_birational` first localizes the finite algebra at
the complement of the contracted prime. That ring is finite over the base
local ring. Identity-on-elements integral coefficient comparison makes its
normalization finite; a second localization gives finiteness at the original
prime with its original fraction-field action. The proof does not assert
that the final selected local ring is finite or integral over the base local
ring. `finite_atPrime_of_isLocalization` preserves those same actions across
the residue-coefficient localization. These two local finiteness transport
lemmas do not require separate Noetherian hypotheses on the two rings.

The final theorem applies the local-to-global theorem to the original
`S`, the original nonzero denominator `a` of `x`, and the original `K`.
The lower module gives the normal principal open `S[1/a] = R[1/a]`.
After an additional localization at a denominator set `M`, the corresponding
open is `M` localized in `R[1/a]`; no equality with the unlocalized open is
used.

The argument corresponds to `nagata-stability-derivation.md`, SHA-256
`4a86145f7e3f4b377f01d8c3030d20b243be688e033969b84744a20e09084edc`,
and its polynomial-value replacement, SHA-256
`5180910e263204d9db9a59b09857d9429cfa3b994d36b749dabf91b11db3cda9`.
[FiniteTypeSurface](FiniteTypeSurface.md) uses this finite normalization
in its monogenic and algebraic finite-type stability arguments. The
coefficient dimension bound remains explicit; no unrestricted dimensional
stability or surface-resolution conclusion is asserted.
