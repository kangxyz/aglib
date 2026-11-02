# The prescribed local surface chain as an actual supported global chain

Source: [SurfaceChain.lean](SurfaceChain.lean).

The surface wrapper derives punctured isomorphy from the actual proper
native chain using the proved proper-birational normal-surface isomorphism
locus. Inputs are an integral normal Noetherian scheme of dimension at most
two, closed nongeneric support point, and the supplied actual proper chain
over its literal stalk. No punctured-isomorphism/algebraization/finite
normalization certificate is imposed as an extra premise.

The output chain has exactly the supplied length, the original terminal
cartesian square, and unchanged complement. The regular wrapper requires
regularity of the supplied local terminal scheme and of that unchanged
complement. It returns a proper integral normal regular source, original
birational field-map isomorphism, and both original pullback projection
equations for the terminal comparison.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/ProjectiveSurfaceChain](ProjectiveSurfaceChain.md).
