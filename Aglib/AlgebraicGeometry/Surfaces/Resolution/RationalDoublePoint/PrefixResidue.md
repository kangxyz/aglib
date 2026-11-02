# Finite original prefix residue extensions

Source: [PrefixResidue.lean](PrefixResidue.lean).

`ClosedPointBlowupPath.transition_residue_finite` proves finiteness of the
residue homomorphism induced by every original blowdown stalk map. The
selected source point is closed by the path data. The actual ordinary
blowdown is proper over its locally Noetherian target, hence locally of
finite type. The existing closed-point residue theorem gives finiteness;
the original `pointStalkIso` transports the specified target point.

`scalar_residue_finite` composes these same homomorphisms over the whole
original finite prefix. No field is replaced by an unrelated isomorphism,
and no separability, perfection or residue-field equality is assumed.

`exists_regular_marked_tail_of_complete_base` discharges the prefix residue
premise of the existing arc theorem. It still requires a genuine marking
on the actual tail, normality of its initial local ring, dimension two of
the original and tail local rings, and completeness of the original local
ring. The existing complete-surface provider derives the normal-completion
conditions needed by the arc argument. This does not construct a marker,
prove finite branching, or prove rational-double-point resolution.

The distinction between a finite original prefix and an unchanged-residue
marked tail is essential. A tail marking provides no information about
residue maps before the tail begins. This leaf instead proves the needed
prefix finiteness from the actual scheme morphisms.

The input path and termination comparison are those of
[Arc.MarkedPath](../../../Blowup/Arc/MarkedPath.md). The finite-type
closed-point argument is the native original-map theorem in
[ResidueTranscendence](../../Birational/NormalizedPointDomination/ResidueTranscendence.md).
The geometric RDP application belongs to [Stacks 54.12](https://stacks.math.columbia.edu/tag/0BGB),
but the present finite-residue result does not use rationality or Gorensteinness.

Present consumers: [BlowupChildren](BlowupChildren.md), [OriginalMixedPath](OriginalMixedPath.md).
