# Artin–Schreier root covers

The lower ring owner [ArtinSchreier](../../../RingTheory/Etale/ArtinSchreier.lean)
defines the actual quotient `R[X] / (X^p - X - a)` for prime `p`. It is finite
and free over every commutative ring `R`, and the structural scalar action is
faithful. When `(p : R) = 0`, the quotient is étale; the premise includes the
zero ring.

[RootCover](RootCover.lean) constructs, for any scheme `X` and
`a : Γ(X, ⊤)`, the actual scheme root cover. Under `(p : Γ(X, ⊤)) = 0` it is
finite, étale and surjective, and its global sections contain an original
`b` satisfying `b^p - b = f.appTop.hom a`. The construction also applies when
`X` is empty. It does not supply the full additive coefficient or
Artin–Schreier sheaf sequence; that remains future work.
