> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#equation-proofs-presentations-and-structure-fields) · [Context](original-context.md) · [Case index](README.md) · [Previous record](whole-library-pass.md) · [Next record](projective-duality-typed-boundaries-before-concrete-geometry.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Equation proofs, presentations and structure fields

These cases were measured on 2026-10-18 while developing the projective
regularity, affine descent and Picard comparison families on the Picard branch. They concern
kernel conversions created by how an equation or a field is written, not
mathematical content.

**Differing proof terms of one equation.** In the Koszul exactness leaves of
`Cohomology/Projective/Regularity/`, three identities elaborated but hit kernel
deterministic timeouts at the default budget; with a local budget of 1000000 the
process aborted at the memory cap, and diagnostic builds reached 25.7 GB.
Profiling isolated the trigger: two occurrences of one coordinate multiplication
or transport carried distinct proof terms of the same degree equation. One
proof was written inline as `by …` in a statement; the other came from another
statement, or was abstracted from a definition body into an auxiliary lemma.
One restated lemma at variable degrees took 114 seconds and 25 GB; the same
statement with a named degree lemma took 2 milliseconds. After every degree
equation became a named lemma with atomic arguments (`koszulDeg_contraction`,
`koszulDeg_shift`, `koszulDeg_wedge`, `koszulWedgeEq`), and spelling conversions
were concentrated in `twistMerge`/`twistMergeInv` stated once at variable
degrees, `Regularity/Koszul.lean` dropped from about six minutes to 6.4 seconds
at a 2.5 GB peak. A candidate explanation, consistent with the next section but
not checked against a kernel trace: the two proofs have differently presented
types, so proof irrelevance still requires converting those types, and that
conversion reaches the twisting sheaves.

**A structure field compared through its unfolded statement.** In the affine
quasi-coherent descent of `Descent/Modules/Fppf/`, the kernel check of the
coherence field `nat_comp` of `specCompTransAlong` against a correct term
exhausted 9 GB even with the inner identity replaced by `sorry`. Stating the
field's proposition as a named definition (`Pseudofunctor.NatCompAlong`) and
building the structure with `CompTransAlong.mk'` made the kernel compare that
definition's arguments; the same check then took about 24 milliseconds in a
scratch probe. The earlier timeouts of the same family came from differing
proof terms inside `mapComp'` (`restrictAlong_mapComp'_hom._proof_*` against new
auxiliary proofs), the pattern of the previous case.

**Two presentations of one object.** In the same family, every comparison that
reached a component of `pullbackCongr` whose arguments were written in two ways
(`Scheme.Spec.map f` against `Spec.map f.unop`; `((specTransApp X).obj M).obj`
against `(tilde.functor _).obj M`) timed out, while each leaf identification
alone checked in seconds. The fix was a transport lemma generic in all of these
presentations (`natCompAlong_of_transport`), whose hypotheses are equations and
`HEq`s between the variables; at `Spec` each is `rfl` or `HEq.rfl`, the kernel
needs about 2 seconds, and the module builds in 22 seconds at 2.6 GB.

**Composites in two presentations.** In the gluing of rigidified pairs in
`Picard/Comparison/`, pulled-back line bundles have two presentations: Mathlib's
`Scheme.Modules.pullback` and the pullback pseudofunctor restricted along
`familyScheme p`. Single objects or morphisms compared across them checked in
milliseconds, but comparing composites (`≫`) whose implicit arguments differed in
presentation cost 7.4 to 15.3 seconds of kernel time per declaration in
development versions of `GluingDescent.lean`; a wrapper definition applied to one
side only gave no gain, and the diagnostics of one such check counted 491,372
unfoldings of `DFunLike.coe` and 435,930 of `ContinuousMap.toFun`. Those
development versions were not retained, so these figures rest on their build logs.
Stating each compatibility on both sides through the regular definition
`CategoryTheory.CompEq f g h := f ≫ g = h` (instances `CompTrans.RigCompat` and
`RigidifiedPair.PairCompat`), and converting presentations once at single
morphisms, brought every kernel check of the module below the 100 ms profiler
threshold; it builds in about 7.5 seconds. In `Comparison/Gluing.lean` the same
restatement cut `originPullback_nat_hom_app` from 21.9 to 12.2 seconds, but only
once the arguments inside `mapComp'` were syntactically the same on both sides
(22.4 seconds otherwise). Two lemmas whose cost appears to lie in their own
`rw`/`simp` proofs barely moved (7.73 to 7.28 and 6.97 to 6.65 seconds). A
candidate explanation, consistent with `lazy_delta_reduction_step` in the pinned
kernel but not checked against a trace: the kernel compares arguments before
unfolding only for constants with regular reducibility hints. `CategoryStruct.comp`
and the projections beneath it (`NatTrans.app`, `Iso.hom`) are abbreviations and are
unfolded down to the underlying data, whereas `CompEq` and `mapComp'` are regular,
so a mismatch directly in their arguments is compared argument by argument.

**Dimension comparisons at variable modules.** `Regularity/Mumford/HyperplaneStep.lean`
(then `Step.lean`) took 91 seconds to build, 77 of them in kernel checking:
`hyperplane_dim_le` 35.3 s, `hyperplane_dim_zero_le` 16.8 s, a connecting-map lemma
8.3 s, and three small `projectiveCohomologyDim` lemmas 3.7 to 5.2 s each. With the same
statements it builds in 9.6 seconds (a standalone profile: 9.0 s wall, 4.6 s kernel)
after four changes. Each dimension comparison is proved once, at variable modules, in
the owner of `projectiveCohomologyDim` (`projectiveCohomologyDim_le_of_surjective`,
`_le_of_injective` and `_eq_iff_injective` in `HilbertPolynomial/EulerCharacteristic`),
for the original linear maps `moduleCohomologyMapOfHom`. Coherence of the first term
`T.X₁ ≅ O(-1) ⊗ F` comes from `prop_of_iso` along the given isomorphism instead of a
`LinearEquiv` between `ModuleCat` carriers. The connecting-map lemmas are stated with the
linear maps. The cores of the two large lemmas are proved for a variable short exact
sequence and instantiated last (`projectiveCohomologyDim_zero_le_of_shortExact`,
`_one_le_of_shortExact`). The added lemmas cost in their owner what its existing small
lemmas already cost (five of the eight take 3.2 to 6.4 s of kernel checking each), so the
net saving is about 57 seconds: 81.4 s less for the step file (builds), and 21.1 s and
3.2 s more for `EulerCharacteristic.lean` and `Exact/Modules.lean` (standalone
profiles). A candidate explanation, not isolated: `projectiveCohomologyDim` is a
`finrank` under the local instance `moduleCohomologyModuleOfHom … projectiveConstants`;
each comparison makes the kernel unfold that instance to match the additive structure of
`Sheaf.H`, and at concrete modules one proof repeats the unfolding for every module
expression.

**Concrete degrees in a statement.** The twisting-functor authors reported that
elaborating a composite written at concrete degrees such as `1 + 0` timed out in
`isDefEq`, while the same composite at variable degrees and the instantiated
lemma elaborated at once. That probe was not retained, so this is an observation
rather than a reproducible measurement.

Practical rules from these cases: give each equation used inside `eqToHom`,
`pullbackCongr` or `mapComp'` one named lemma with atomic arguments and reuse its
proof term; state such lemmas at variable objects or degrees and instantiate last;
state a structure field that compares badly through a named definition; prove the
comparisons of a definition that carries a local instance once, at variable objects,
in the definition's owner, so that consumers only instantiate them; compare an
equation of composites across two presentations through one named regular definition
stated on both sides, keeping the arguments beneath projections (such as `mapComp'`
components) syntactically identical; and before
restructuring, separate elaboration from kernel cost with
`set_option debug.skipKernelTC true` in a scratch copy. A structural diff of the two
compared terms (a scratch tactic printing both goals) located each mismatch above
in seconds.

