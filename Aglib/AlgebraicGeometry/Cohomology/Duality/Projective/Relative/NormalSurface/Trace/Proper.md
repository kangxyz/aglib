# Ordinary proper canonical trace

`Proper.lean` constructs `normalSurfaceProperCanonicalTrace` on the actual
`h_*omegaY`, proving its finite type by native proper coherent finiteness and
the original degree-zero comparison. The base is a regular local domain;
sources are integral, normal, dimension at most two, with actual closed
projective embeddings, dominant structural maps, finite generic image maps,
and their original structural triangle. No later stalk is assumed finite over
this base. The canonical modules are their original degree-n homology.

Write `E` for `normalSurfaceFiniteCoherentSerreAddEquiv`, `s` for the native
right-derived-single unit, and `C` for the actual derived-global-sections
composition with the original scalar triangle. The formula is

    tau = EX.inverse(RΓX(s(omegaY)) ; C.inverse ; EY(identity)).

More generally the functional of `a : M → h_*omegaY` inserts `single(a)`
before `s`. Its contravariant naturality and coherent Serre injectivity prove
that its inverse at every coherent M is exactly `a ; tau`. The explicit mate
lemma identifies this functional with the original pullback unit followed by
the Serre functional of the original ordinary adjunction mate of a. At a=identity
that mate is the counit. Thus this is the coherent-Yoneda construction, not a
faithfulness assertion about global sections or a general proper right adjoint.

Mathematical source: fixed global-canonical `PROOF_CONTRACT.md` §§2–3, SHA256
`d5c74aa2686b332ee1253f90506df93199ef30935de25741ba9b9fb49fdb479e`.
Its ordinary conditional review is not native closure. The present construction
uses the equivalent native-single-unit expression and proves the mate equation.

Remaining assembly: identity/composition coherence for the exact original derived
comparisons; full local-spectrum counit/evaluation compatibility; local Ext
normalization at all generizations. No canonical surjectivity, trace invertibility
for arbitrary proper maps, Gorenstein modification or resolution is claimed.
Compiler/audit status is recorded by the integrator's graph.

## Exact composition obligation

For an arbitrary ordinary upstairs module M, set

    V_h(M) = RΓX(s_h(M)) ; C_h(M).inverse.

Naturality of the original single unit and C proves V_h natural in M.
The remaining whole-derived coherence is

    RΓX(single(pushforwardComp(g,h)_M)) ; V_(g;h)(M)
      = V_h(g_*M) ; V_g(M).

Its identity counterpart retains `pushforwardId`, not a definitional replacement
of the actual pushforward functor. These equations must follow from the native
whole derived composition units, before any precomposition by ordinary sections.
Once proved, the trace-composition calculation is: apply EX at the coherent
source h_*g_*omegaW; naturality of V_h transports h_*tau_g; the defining EY(tau_g)
is V_g followed by EW(identity); the displayed equation gives the functional
of `pushforwardComp ; tau_(g;h)`. Coherent EX injectivity then gives equality
of the actual sheaf maps. This route is equivalent to the pullback-unit route
in the contract and avoids an unnecessary pullback coherence expansion.
