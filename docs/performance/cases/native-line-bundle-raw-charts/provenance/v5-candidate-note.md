# Raw-chart naturality: shared whole-equation candidate

Status: applied to the single owned native file after the principal's snapshot
release and HEAD/input-hash guards. No compiler invocation or performance
improvement is claimed. Native execution remains with the principal.

The input is `AssociatedBundle.lean` at native HEAD
`54d6974ace11bf7d197aa925cb8cade86db8a24f`, with SHA-256
`d5550c87c483ad794b02df2e07931c11bb2e5882d54adce1dbe52df0c791c166`.
The candidate has SHA-256
`844a9cc1d6615ee5ef6bdb54afbf1f76eae68f5bc8adbab6112162555be58a0d`.
The complete input/output files, exact unified delta and metadata are adjacent.

The fixed argument is unchanged. For `f : U ⟶ V`, apply `hr` to the original
indices `⟨U.unop, s⟩` and `⟨V.unop, P.carrier.obj.map f s⟩`, with refinement
arrows `f.unop` and `𝟙 V.unop`. The second restricted torsor section is the
first one by the actual functor's `map_id_apply`. Hence the original unit
argument is `1` by `hu`. The native `transition_self_one` identifies the
original transition with the identity. The native `pullHom_id` identifies the
identity restriction of the second original local chart with that chart.
Canceling this transition gives naturality via the already proved original
presheaf-map equation.

The encoding change shares that complete composite equation. The private
regular definition `ChartComposition f t g := f ≫ t = g` is used both by the
definition of `ChartRelationOn` and by the generic identity cancellation proof.
Thus its specialization compares the three actual maps as arguments before
unfolding their composite. This is a local equation representation, with no
new category, realization, data record, site, cover, frame or mathematical
premise. Unfolding it restores the previous `ChartRelationOn` body exactly.
The public declaration signatures are unchanged.

The old concrete `simpa only` is replaced by three fully typed equations:
torsor/unit normalization, the actual transition identity, and the actual
identity-base restriction. The cancellation helper proves the same whole
morphism equation over variable category objects. It neither unfolds the
line-bundle pseudofunctor nor asks arbitrary local charts to extend globally.
The existing private `presheafHom_map_eq_pullHom` and `hview` are unchanged.
`rawPresheaf`, all chart values, unit/counit maps, positive transporters and
the complete source after `sectionFamily_natural` are unchanged.

This responds to native run `remote-664a5fa3fb36457da4e86e36c7088ea6`, which
reported a `whnf` timeout at the original `hrestrict` simplification and its
declaration, followed by the missing-constant cascade at `rawChart_natural`.
It uses the owning performance guide's shared-equation and whole-comparison
methods. The record does not identify an exact Lean reduction pair or establish
a measured compiler cause. Ordinary native compilation of AssociatedBundle and
its actual PowerDescent consumer, then the principal's final scoped checks,
remain required.
