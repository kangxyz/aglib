# Positive twists from an actual projective embedding of P1

The target is the original native `ProjectiveSpace k (ULift (Fin 2))`, over an
arbitrary field k, with the original structural map. For a finite original
coordinate type I and an actual closed immersion into `ProjectiveSpace k I`,
the file constructs a positive integer d and an actual module-sheaf
isomorphism between the pullback of O(1) and O(d) on that same native P1.
The over-k wrapper retains the original structure triangle. Transport to an
actual specified line bundle uses its actual pullback comparison.

The argument first classifies all actual P1 line bundles by the existing
residue-weighted Picard degree. Native genus-zero Riemann–Roch gives a nonzero
section of every degree-zero line bundle; the existing section-rigidity
producer then supplies its actual trivialization. This makes degree
injective. The original degree-one homogeneous polynomial basis and native H1
vanishing compute degree O(1)=1; native tensor multiplication gives degree
O(d)=d and hence actual module-sheaf classification.

For positivity, apply the single closed-embedding Serre producer in
`Cohomology/Projective/SerreVanishing/ClosedImmersion` to O(-2). If the actual
pullback of O(1) had nonpositive degree, its large tensor twists with O(-2)
would have degree at most -2. Riemann–Roch and Serre vanishing would give a
negative dimension for actual H0. Thus the original pullback has positive
degree. No algebraic closure, perfectness, characteristic restriction, desired
twist comparison or representability theorem is assumed.

The main APIs are `ProjectiveSpace.Line.exists_positiveTwist` for an original
over-k embedding and `exists_positiveTwist_of_comparison` for an actual
specified line bundle. The underlying strict-positivity theorem needs only the
actual closed immersion; it is stronger than the over-k application.
