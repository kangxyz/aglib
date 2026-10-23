# The original coefficient field of a projective-line embedding

The source is EXACTLY native P=ProjectiveSpace κ (ULift.{u}(Fin2)), with its
original toSpec κ map and original κ action. A, κ and I have the same explicit
native universe u; A is any commutative ring, κ any field. The canonical-map
and twist comparisons need no finiteness of I. The positive-twist consumer
retains only the field producer's finite-I condition.

For an ORIGINAL t:P→ProjectiveSpace A I, coefficientHom t is the actual
A→κ ring homomorphism obtained by composing its original structural
appTop map with ΓSpecIso A inverse and the inverse of the ORIGINAL
κ→Γ(P) coefficient equivalence. No algebra structure, coefficient-field
embedding or desired base triangle is an input. coefficientHom_coefficient
states exact recovery of the original structural coefficients, and
coefficientHom_base proves the original scheme base triangle using native
faithfulness of global sections into an affine target.

coefficientLift t is constructed by the actual native projective coefficient
Cartesian square. coefficientLift_comp recovers the ORIGINAL t;
coefficientLift_toSpec makes it an actual morphism over the ORIGINAL κ.
coefficientLift_baseChangeIso identifies its composite with the canonical
base-change iso as exactly the literal pair map to
P_A×_{Spec A}Specκ. The existing maps and base-change iso are reused.

If t is closed, coefficientLift_isClosedImmersion proves the SAME lift
closed. Specκ→Spec A is affine, hence separated, and its actual coefficient
base change is separated. Native IsClosedImmersion.of_comp applies to the
original closed composite. Neither flatness nor finiteness of A→κ,
Noetherianity of A, injectivity of its coefficients, nor perfectness of κ is
assumed.

For every integer d, coefficientLiftTwistingIso is an ACTUAL isomorphism
between the original t-pullback of O_A(d) and the lift-pullback of O_κ(d)
on the SAME P. It is the native pullback congruence/composition comparison
followed by the existing arbitrary-ring twistingPullbackIso, without a
flatness premise or a chosen frame family.

The theorem exists_positiveTwist_of_isClosedImmersion_over_ring applies the
proved field theorem exists_positiveTwist to coefficientLiftOver t, whose
left map is the same closed coefficient lift. It composes the resulting
actual positive comparison with coefficientLiftTwistingIso t 1. Thus, for
finite I and an original closed t, it produces a natural d>0 and an actual
isomorphism t*O_A(1) ≅ O_P(d) on the same native projective line. The
original κ action and original t are retained throughout; no positive-twist
family or chosen degree is an input. This conclusion uses the actual
Line/PositiveTwist proof, rather than a supplied positivity premise.
