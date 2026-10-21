# Ordered cycle coordinates on the original component maps

The many-component case keeps the original finRotate order. The two-component case uses the same full shared pair and reverses the strict component's endpoint order exactly once. The original geometric strict-recognition conditions remain explicit; the actual étale chart theorems supply regularity and smooth-stalk inputs internally. Forward compatibility is proved on actual source pullbacks and backward compatibility independently on the actual polygon target pullbacks.

- `coordinateIso`: the ordered actual component P1-to-glued-line isomorphism over the original residue field.
- `coordinateIso_forward_compatible`: scheme-valued compatibility on pullback(componentMap i)(componentMap j).
- `coordinateIso_backward_compatible`: independent compatibility on the literal target-component pullbacks.

The source ranges and hashes are retained in the Lean header. The same actual
objects, structural maps and point orderings are used. No model, minimum,
regularity, or contraction existence is supplied by this extraction.
