# Actual Chow domination by point blowups

`exists_pointBlowupChain_chowDomination` starts with the actual proper map
`q : Z ⟶ Spec A`, where A is Noetherian and Z is integral, regular, Noetherian
and of topological dimension at most two. It applies the native projective
Chow theorem and keeps its original modification `π : W ⟶ Z`, its closed
embedding `j` into finite standard projective space, its dense isomorphism
open V, and the equation `j ≫ toSpec = π ≫ q`.

The generic map is constructed from the inverse of `π ∣_ V`, using the
original generic-stalk morphism of Z. The native projective-extension theorem
then constructs an actual `PointBlowupChain β`. Each centre in that chain is
an actual closed point whose local ring has dimension two. The source Y stays
integral, regular and Noetherian, with all stalk dimensions at most two.

The extended projective map h factors through the original W. To prove this,
pull back the original closed immersion j along h. The generic compatibility
gives a dominant map into this pullback, so its closed projection to Y is
dominant and surjective. Since Y is reduced, that projection is an isomorphism.
Its inverse constructs `a : Y ⟶ W`, with `a ≫ j = h` and the exact generic
triangle through the original `functionFieldMap β`.

Generic agreement and separatedness of q prove `a ≫ π = β`. Both original
base triangles and the generic triangle for h are returned as well. No
integrality, normality or regularity of W is assumed. The lower theorem
`exists_pointBlowupChain_dominating_projectiveModification` takes a supplied
closed projective modification; it requires only separatedness of q and a
finite projective index, with no Noetherianity assumption on A.

This is the P2–P3 construction for general proper-map contraction. Projectivity
of the top blowup stage and its descent down the chain are separate consumers.
Native compiler evidence is supplied separately for the frozen source bytes.
