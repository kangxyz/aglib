# A specified algebraic closure inside an ambient field

`RelativeImage.lean` identifies a supplied `IsAlgClosure F L`, under its specified
embedding into `K`, with the literal `algebraicClosure F K`. Its equivalence and
transported automorphism preserve that embedding on every element. The three
fields may have different universes. This construction neither completes a field
nor supplies an algebraic-closure witness for a completion.

The period descent consumer uses the actual relative algebraic closure in
[`Units/CyclicQuotientDescent`](../Units/CyclicQuotientDescent.lean).
