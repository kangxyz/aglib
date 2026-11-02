# Artinian total quotient rings

`IsFractionRing.krullDimLE_zero_of_isReduced` proves that a reduced Noetherian
ring which is its own total quotient ring has dimension zero. Every maximal
ideal is associated by the native Noetherian total-fraction-ring theorem.
Its actual annihilator witness x does not belong to that ideal: otherwise
x squared is zero. Every smaller prime therefore avoids x and must contain
the whole annihilator, so equals the maximal ideal.

`IsFractionRing.isArtinianRing_of_isReduced` applies this to any supplied
genuine total quotient ring, using preservation of Noetherianity and
reducedness under the original localization map. The native `FractionRing R`
specialization is `FractionRing.isArtinianRing_of_isReduced`.

There is no dimension bound or domain hypothesis on the reduced Noetherian
source. In particular this lemma does not assert that generic formal fibres
of quasi-excellent rings are zero-dimensional; the total quotient ring and
such a generic fibre are distinct objects. Integral closedness and local
ring domainhood remain separate consequences requiring additional arguments.
