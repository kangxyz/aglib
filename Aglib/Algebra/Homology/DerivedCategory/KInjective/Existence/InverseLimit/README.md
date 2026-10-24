# Entire-predecessor inverse limits

This family implements the compatible-primitive route of Stacks 0AAT on native
cochain complexes of abelian groups and native categorical limits. The index is
a small well-founded partial order, including ordinal initial segments. The
index universe `w` and coefficient universe `u` remain explicit and independent;
only actual evaluated-diagram limit instances are retained, without assuming
arbitrary limits of the index shape or silently resizing.

- `CoherentChoice`: actual well-founded dependent choice and its compatibility.
- `Elements`: element families transported through native limit cones.
- `Predecessors`: all strict predecessors, original stage cone and comparison.
- `PrimitiveFamily`: correction against the entire predecessor limit.
- `Recursion`: actual simultaneous primitive recurrence.
- `Exactness`: native limit exactness with an explicit intermediate predecessor
  exactness hypothesis.
- `Nested`: original nested predecessor diagrams and comparison isomorphisms.
- `Acyclic`: well-founded induction discharges predecessor exactness, then proves
  acyclicity of the full native limit.

The theorem requires degreewise surjectivity to the entire predecessor limit at
every stage. Pairwise transition epimorphisms do not suffice. This family does
not construct an exhaustive source filtration or a global K-injective replacement.

Compiler acceptance covers `CoherentChoice` in graph 056 and `Predecessors` in
058. The original `Elements` and `PrimitiveFamily` were accepted in 056/060;
root explicitly released their signatures for the necessary universe-safe
generalization. Their historical receipts do not validate the modified bytes.
The full generalized consumer closure is submitted, not yet accepted evidence.

The universe-safe closure through `Acyclic` was accepted in graph 070, with
`Recursion` and the generalized element/primitive helpers accepted in 066 and
`Nested` in 068. Thus the final native inverse-limit acyclicity statement has
actual compiler evidence, distinct from final audit evidence.
