# Affine higher-degree field stages: share the original statement and producer

This is a completed repair of Aglib/AlgebraicGeometry/EtaleCohomology/Fields/TwoFieldEffacement/AffineEtaleHigherDegree.lean on the actual selected main/fa8 integration input. The final ordinary production check passed. Failed and bounded diagnostic runs retain their own input identities; this is not a matched speedup experiment or an identification of a unique compiler cause.

## Original field and failure boundary

The original public hypotheses are a nonempty smooth geometrically connected affine curve p : U → Spec k, a sheaf F from Spec k killed by a positive n that is a unit in k, q ≥ 2, and the original standard-Ext class. Its finite-constant presentation produces the actual finite-Galois L : FiniteGaloisIntermediateField k (SeparableClosure k). The higher constant-class supplier produces s : Finset (AlgebraicClosure L) and the literal field

    E := separableClosure L (finiteField L (AlgebraicClosure L) s)

The conclusion retains finiteness over k, the original two-stage Etale map Spec.algebraMap L E ≫ Spec.algebraMap k L, and literal original-class zero along the two original pullback projections.

The original 7fa source reported requests for Algebra (SeparableClosure k) (finiteField L (AlgebraicClosure L) s), followed by an isDefEq timeout. Candidate c517 selected the same E.algebra and Algebra.toModule for L → E and inferred the original fully explicit coefficient-class producer before unpacking it. Its actual check still reported that ambient-algebra goal at Module.Finite k E, missing SmoothOfRelativeDimension 1 r for the original pullback, and a whnf timeout.

The inspected Mathlib source was pin d13f23b723b8a846827a245b89c10fc7d3f11612, IntermediateField/Basic.lean:405–454, SHA 1ddd696fbd51d9f38d6941e2761652bfe7fb88dccf1addab7b55e3a984d60d98. It contains inherited module/algebra and shortcut instances with ambient algebra arguments. The reported ambient action is not a mathematical input here. No trace isolated the exact search or reduction path; the error line numbers do not establish one.

## Completed repair

The repair explicitly selects the original restriction action k → L → E:

    letI : Algebra L E := E.algebra
    letI : Module L E := Algebra.toModule
    letI : Algebra k E := ((algebraMap L E).comp (algebraMap k L)).toAlgebra
    letI : Module k E := Algebra.toModule

One public transparent predicate, AffineEtaleHigherFieldStage, defines the entire original finite/Etale/zero conclusion over variable k, L, r, f, M, q, c and s. Both the complete producer and public finite-Galois conclusion use this same regular head. The native public statement therefore does not separately elaborate the nested field-stage implementation. Unfolding returns the same literal E, field maps, scalar restriction and zero equation. This is not a new record or an added input certificate.

The private producer completes the original argument over variable L and the actual input scheme/maps V, r and f before finite-Galois/pullback specialization. It calls the existing constant-class supplier once and retains its s/E and zero. It proves the original tower by IsScalarTower.of_algebraMap_eq' rfl, finiteness by Module.Finite.trans L E, and Etale by composition of the original two Etale maps. The already proved cohomologyPullback_zero_of_constant_coefficient_composite transports the same d, coefficient arrow, presentation equality and zero to the literal original class. The source world eX stays independent of standard u + 2.

The native caller retains the original inferred hclass, witnesses and coefficient arrow. It supplies the accepted sibling's exact SmoothOfRelativeDimension base-change witness using IsStableUnderBaseChange.of_isPullback and the original IsPullback.of_hasPullback square, plus the same geometric-connectedness witness. These are proved consequences of the original hypotheses. Finally, seven proof-local letI bindings were changed to let to satisfy the existing style.haveILetI rule; their bound values did not change.

| Item | Original value retained |
|---|---|
| Public premises | Same k, U, p, F, n, positivity, annihilation, unit, q ≥ 2 and original class |
| First field | L from the original exists_finiteGalois_constant_class application |
| Finite coefficients | Same B, additive/finite instances, n-torsion, t, d and hd |
| Coefficient arrow | Same e.inv ≫ (inverseImage f).map ((inverseImage p).map a) |
| Pullback | r = pullback.snd p (Spec.algebraMap k L); f = pullback.fst p (Spec.algebraMap k L) |
| Second field | Same s and E = separableClosure L (finiteField L (AlgebraicClosure L) s) |
| Scalar action | Original L → E map, restricted along the original k → L |
| Finiteness/Etale | Same finite L-stage and finite-Galois k/L; original Etale proofs and their composition |
| Literal zero | Pullback along pullback.fst r (Spec.algebraMap L E) ≫ f on the original class |
| Ext worlds | Producer source eX independent; constant/final stages standard u + 2; public source remains its original standard u + 2 |

No Algebra (SeparableClosure k) action on the finite stage is assumed. No field, embedding, cover, coefficient realization, public premise, global instance, axiom, option, heartbeat, memory allowance or check suppression was added. The two stages remain separate.

## Retained evidence

| Input and question | Native source/run | Result and scope |
|---|---|---|
| 7fa69a76, original production | f5b101c5 / remote-e63f38c0cd734762bc00914e9586403f | CPP1, 1987.949259 s; ambient-algebra and isDefEq errors |
| c5177efa, L → E pins and inferred presentation | e6375742 / remote-51ff334d31394499936b7c346ff080b0 | CPP1, 2325.700010 s; Algebra (SC k) goal51:6, missing Smooth71:37, whnf20000035:0 |
| ef1e578f, statement-only probe ca5b60bd | e8fbad86 / remote-35e07cb56c484839b01c5729c862a491 | Exact setup0; formation124 at300 s, reported elapsed305.265129 s, empty log. No helper/production proof was in the probe; no production CPP launched |
| 8a26d5fb, shared predicate and complete producer | dc258e18 / remote-bbb44c32f5f140ec90c7a8c7ec3e683a | CPP1, 55.204979 s; only seven style.haveILetI errors78–84 reported; not CPP0 |
| f94e43ca, exactly seven letI → let changes | 5a7948eb / remote-1a2a5647acb94d36b30e695d861afbfc | Actual CPP0, 56.777508 s; command0, one successful compiler invocation, group_closed true |

Production timings are native module elapsed times, not preparation time or summed parallel batch wall time. The probe bound/elapsed is a different measurement mode. No unchanged long failure or second probe was repeated. The empty probe log does not identify an internal phase or a failure in the absent proof.

Final source SHA:
f94e43ca02bf427be2a016f4b0602789e01ba0fcf70e02f9eaa72fa332dc7edd.

Final native frozen source:
5a7948ebebc1e3d0f8d8ef3c9309d81ede33df0a716d130bca145af7a764ce7e.

The authoring checkout was guarded at HEAD6564f1ad588229d833b2cf87102237e7a4b32bfb. The native overlaid checkout receipt reports HEAD2f17670f9ade927deeb6ea21d1c50c67a9e7842d. The source-content hash binds the actual native input; those HEADs are not identified as the same tree.

The unchanged profile was jobs8, threads4, Lean M12800 MiB, RSS cap65536 MiB, default checks; Lean4.34.1, commit5045d0056413266e57c625dcd7c365b10e377c52; Mathlib d13f23b7. The recorded command inside the admitted native wrapper was:

    lake --rehash build Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.AffineEtaleHigherDegree

The wrapper supplied the recorded source, setup, profile and compiler -j4 -M12800. Compatible dependencies were reused. This is retained reproduction information, not a request for another run.

[Source and invocation provenance](evidence/provenance/SOURCE.json) records full source/run hashes, supplier hashes, command, profile, pins and original absolute locators as historical provenance. Portable evidence is retained here: [source snapshots](evidence/sources/), and receipts, logs and events for [7fa](evidence/runs/7fa/receipt.json), [c517](evidence/runs/c517/receipt.json), [ca5 statement probe](evidence/runs/ca5-probe/PROBE-RESULT.json), [8a26](evidence/runs/8a26/receipt.json) and [f94e](evidence/runs/f94e/receipt.json). The probe's empty formation log is preserved as such. [READY-006](evidence/provenance/READY-006.json) records the original intake provenance; earlier runs are not relabeled as final-source evidence.

The subsequent [independent ordinary affected review](evidence/review/review-01.txt) accepts final f94e on its recorded source basis. Its source/math verdict is separate from native checking, performance and whole-integration acceptance.

## Coverage and reuse boundary

The final check covers the actual production statement, shared stage definition, complete variable-L producer and native specialization. This native check is separate from the independent ordinary review and supplies no broader integration verdict. Source inspection found no direct theorem consumer beyond the existing algebraic-geometry umbrella; no separate client or full umbrella check was added.

This repair combines explicit original scalar actions, existing geometric dictionaries, a shared transparent conclusion and completion of the coefficient/field argument before concrete specialization. The observations do not isolate a unique internal cause or establish a matched speedup. Reuse the method when the same chosen construction and complete statement can be shared at variable inputs, retaining actual maps, scalar actions, independent worlds and complete obligations.

