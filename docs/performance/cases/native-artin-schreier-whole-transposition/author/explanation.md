# AS native transposition: fixed argument and evidence boundary

The compiled repair moved the whole equation for the original transposed map across a variable-adjunction boundary. Replacing only the zero-transpose subcalculation with the native additive HomEquiv law had left the final concrete specialization expensive. The useful distinction is the returned map: the successful helper concludes `k ≫ g = 0` for the actual supplied k, rather than asking the caller to identify a reconstructed `(adj.homEquiv ...).symm i` with k.

## The unchanged mathematical content

The selected ring-valued presheaf R, its native single additive ULift and its original supplied sheaf proof are used throughout. Frobenius is the existing `RingHom.frobeniusOfPrimeCastEqZero` objectwise; restrictions use `map_pow`. The objectwise assumption is p=0, including zero rings, not exact characteristic p or Nontrivial. The original residue constants use `ZMod.castHom`, and the original sheaf map is the native sheafification-adjunction transpose. Its whole toSheafify/unit equation remains the same. Subtracting the original identity gives the actual Artin–Schreier arrow.

The original presheaf composite is zero because map_pow and `ZMod.pow_card` send every residue constant to itself. This calculation was preserved. The public Scheme wrappers keep the actual section rings, the p=0 supplier from Γ(X)→Γ(U), old FQNs, the original prime-field constant sheaf, the original adjunction unit and literal scalar/AS values. Site object/Hom, ring and lift worlds remain independent; the coefficient output is the native max of ring and lift worlds. Only the existing HasWeakSheafify hypothesis is used. No generic local injectivity, kernel, AS epimorphism or exactness statement is added.

## Why the whole helper proves the right equation

Let D and E be preadditive categories, L ⊣ U the original adjunction, and U additive. Use the actual data

```
P : D, A B : E
 i : P ⟶ U.obj A
 k : L.obj P ⟶ A
 g : A ⟶ B
hk : adj.homEquiv P A k = i
hz : i ≫ U.map g = 0.
```

The native `left_adjoint_additive` gives L.Additive. Native naturality, with X=P, Y=A and Y′=B supplied explicitly, gives

```
adj.homEquiv P B (k ≫ g)
  = adj.homEquiv P A k ≫ U.map g
  = i ≫ U.map g
  = 0
  = adj.homEquiv P B 0.
```

The last equality is native `homAddEquiv_zero`; injectivity of the same HomEquiv yields exactly `k ≫ g = 0`. The private helper `transpose_comp_eq_zero` proves this full calculation over variable categories/functors/adjunction data before specialization. It introduces no new adjunction or model.

The concrete caller supplies fully typed P₀, A₀, i₀, k₀ and g₀ at the literal native `presheafToSheaf.obj` head. Here k₀ is the existing prime-field-to-additive map and g₀ the existing AS map. The existing whole `toSheafify_primeFieldToAdditive` theorem proves hk₀; the unchanged ring calculation proves hz. These are supplied proofs from original data, not extra desired-law premises. The caller then instantiates the completed helper once. The prior concrete inverse-HomEquiv/naturality/congrArg/trans chain is absent.

## What the diagnosis actually located

Frozen source 4d4bf8cf failed at whnf/200000 in run 64d200; source 4f745918, using the native inverse-zero API, failed at the same standard bound in run a5e349. Earlier syntax/type repairs are preserved separately in repair-1 through repair-4 and must not be reclassified as this performance diagnosis.

The single 9b504 probe used a faithful theorem-binder formation check `(_h : P) : True`, then the exact current proof with compact phase messages and scoped diagnostics/simple profiler/named header/value/Kernel traces. Its formation header, value and named Kernel check succeeded (log lines 8–25). Every actual-body marker through before-final-transport was reached (38–42). The final exact tactic then timed out at whnf/200000; its actual value trace failed (138–147). There was no named Kernel check for the AS theorem. Thus the observed frontier was final exact-term elaboration/specialization or expected-type conversion, after hz, the additive dictionary and the native inverse-zero phase. The probe did not identify the exact compared expression pair.

Its 19.6-second exact tactic and 19.7-second cumulative tactic total are profiling observations. The 10 ms kernel total belongs to formation/prefix/auxiliary checks, not a successful AS-theorem kernel check. Repeated presheafToSheaf/leftAdjoint/Classical.choose unfolding counts (403629 each) are relevant clues, not per-constant timings or proof of a particular reduction pair. The post-error command-end marker is not success evidence.

## Actual closure and known limits

The final full lower source is 87ff6356. Closed run ca150085 compiled exactly that lower module with one fresh frontend: receipt elapsed_seconds 13.083733141422272, log module time 3.9s, exit 0. Closed run 03a7acc9 compiled the two already-refactored wrappers 5be6b57f/d2a7c746 with two fresh frontends: receipt elapsed_seconds 11.12849646806717, module log times 3.5s/4.2s, exit 0. Their full source archives match these three hashes, and both receipts report no input drift. Native default 200000 heartbeats, -j4, -M12800 and default trust were retained. Source snapshots, archive hashes, complete commands and exact log/receipt locators are in evidence.json; core-six.md names six full frozen source files.

These are source-matching incremental passes for the lower module and two unchanged-value Scheme adapters. They do not cover untouched Injective/Complex/Surjective/ShortExact, the complete AS sequence or the overall étale migration. Failed runs, an instrumented probe and later passing runs are not a matched timing experiment; receipt elapsed, wall, module-log and profiled tactic times must not be substituted for each other or summed into a speedup claim. No exact conversion-pair, RSS/per-file memory attribution or universal future-budget claim is supported.

This packet explains a current compiled argument for a support writer to integrate as one complete performance case plus one main-guide method. It reuses the existing logs/snapshots and adds no build, profile, benchmark, replay, re-audit or acceptance cycle. Production source/docs/registry/Git/remote state was held unchanged.
