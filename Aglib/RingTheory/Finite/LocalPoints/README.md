# Actual finite local ring points

This chain keeps one actual maximal localization, its residue map and the
unique finite purely-inseparable residue embedding into the fixed algebraically
closed Ω. [ResidueEmbedding](ResidueEmbedding.lean) and [LocalPoint](LocalPoint.lean)
construct the actual ring maps and their value/uniqueness equations.
[Kernel](Kernel.lean) proves the exact closed-base kernel and component selection;
its kernel-comap lemma does not require finiteness. [Component](Component.lean)
and [Equiv](Equiv.lean) reconstruct and classify the actual common-field points.

R/A/Ω universes remain independent. The original local/Henselian, finite-algebra,
separably-closed residue and algebraically-closed target hypotheses are retained.
Residue fields are not identified with Ω and points are not replaced by supports.
The old ExactImageComparison ring aliases and actual Spec.map/stalk consumers
retain the original values; there is one lower implementation of the chain.
