# Finite etale multiplication over arbitrary fields

`multiplication_finite_etale_of_invertible` proves that the literal morphism
`(𝟙 G.X) ^ n` is finite, etale and surjective for every native
`G : Grp (FScheme k)` satisfying the original `Curve.Properties G.X` and every
natural `n` with `IsUnit (n : k)`. The field has arbitrary characteristic and
retains universe `u`. Positivity is unnecessary once the scalar is a unit.

`multiplication_etale_of_isUnit` supplies the etale conjunct separately.
`pointedGroupLaw_multiplication_finite_etale_of_invertible` retains the exact
`GrpObj C` stored by the original `PointedGroupLaw C c`; its conclusion concerns
that same literal power map.

The proof uses the original maps in this order:

1. `MultiplicationCotangent.lean` gives scalar multiplication by `n` on the
   actual identity cotangent quotient. A unit scalar makes that map surjective.
2. The section-induced residue equivalence and preservation of the actual
   structural constants show that the pointed local endomorphism induces the
   identity on the actual residue field. The local map is essentially finite
   type because the original scheme map is locally finite type.
3. `RingTheory/Etale/LocalCotangent.lean` applies Nakayama to the actual
   cotangent map and proves formal unramifiedness of the original identity
   stalk map.
4. `stalkMapAt_functionField_square` proves the commutative square between that
   local map, the original `functionFieldMap`, and the actual
   stalk-to-function-field localizations. Formal unramifiedness passes to the
   original generic-field map. Its finiteness is supplied by the already proved
   finite multiplication morphism; the native field criterion makes it
   formally etale in every characteristic.
5. The actual generic stalk then supplies a nonempty etale source neighborhood.
   Over an algebraic closure, the existing native group-translation theorem
   spreads this neighborhood to the whole homomorphism.
6. The actual monoidal pullback functor preserves the literal power map. The
   explicit pullback square and faithfully flat descent therefore prove
   etaleness of the original-field multiplication morphism.

No differential, nonconstancy, flatness, separability or etaleness theorem
family is supplied. The intermediate local map is only essentially finite
type; no finite-presentation or finiteness assertion about a localized
identity stalk is used. There is also no DVR flatness premise or detour.

The assigned source target is the finite and etale part of
`EllipticMultiplicationGeometry` in
`R5Lab/AlgebraicGeometry/EllipticCurve/Isogenies/CyclotomicDualKernel.lean:283–286`,
supplied source SHA-256
`9e41c9cb806d7b989f7827341fb0c9e54fbcc2276d8f006efcc11b17aedb99a4`.
Both of those conjuncts are now proved on the original maps and hypotheses,
including positive characteristic. The previous positive-characteristic
etaleness frontier is superseded by this result.

The remaining conjunct `HasGeometricDegree ... (n * n)` is not proved here.
Rank-two torsion coordinates, Weil/Cartier pairings and Picard/Hilbert
representability remain separate. The current native consumer is
`Group.MultiplicationKernel`: its existing literal kernel is finite etale after
base change along the original identity section. Finiteness of its point
carrier does not supply a degree or a basis.

Only ordinary production compilation was run. No client file was added, and no
client check, kernel replay or additional acceptance chain was run. Existing
providers and the preceding producers remain read-only in the original
checkout. Publication may apply the principal's declared module-path
canonicalization without changing these mathematical interfaces.
