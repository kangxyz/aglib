# Finite singular sets on affine opens

`Scheme.finite_singularSet_inter_affine_of_finite_compl_regularLocus` takes an
actual affine open U and finiteness of the complement of the regular locus
of its section ring. It proves finiteness of the nonregular actual scheme
stalks in U, using the original `fromSpec` map and its stalk isomorphisms.

There is no global affine base, normality, dimension bound, Noetherianity,
or nonemptiness hypothesis. Those conditions belong to the supplier of the
finite ring-locus complement. The proof is the single affine/stalk transport
extracted from the surface `FiniteSingularLocus` theorem, whose former
interface is retained as a caller.
