# The actual sequence of two generating sections

For any native scheme X, let L be an actual LineBundle X and let
s : ULift.{u}(Fin 2) → (unit_X → L.val) be the original pair. The sole
generation hypothesis is Epi (Sigma.desc s). No field, Noetherianity,
flatness, global frame, projective embedding, or desired kernel comparison
is supplied.

The object twoSectionSequence L s is a native ShortComplex X.Modules.
Its three objects are exactly (dualLineBundle X L).val, the original
coproduct of the two structure modules, and L.val. Its second arrow is
literally Sigma.desc s. Its first arrow twoSectionKernelMap L s is the sum
of minus InternalHom.dualSection X (s 1) followed by the original zeroth
coproduct inclusion, and InternalHom.dualSection X (s 0) followed by the
original first inclusion. The existing dualSection is actual internal-Hom
precomposition followed by evaluation Hom(unit,unit) ≅ unit.

The public projection equations recover precisely the signed pair
(-s1*,s0*). Their apply variants identify the values on every original
open as minus evaluation of the original dual section on s1(1), and
evaluation on s0(1), respectively. Thus the left object is the actual
native dual, and both arrows retain the original maps. The first arrow's
composite with the original row is proved zero without the Epi premise.

The proof of twoSectionSequence_shortExact uses the existing lower
Modules.LocallyFree.LocalSplitting.exists_local_section_of_finite_basis.
An actual local unit frame of L gives its existing singleton free basis.
The original sheaf Epi admits simultaneous local lifts of that basis, so
after shrinking it has a genuine right inverse h on the same line chart.
This is a local sheaf lifting argument; it asserts no surjectivity of
global sections or global projectivity.

In the actual line and dual frames, write the original row as (u,v) and
the right inverse as (a,b), where ua+vb=1. The signed original first arrow
is (-v,u), and (-b,a) is its retraction. The identities rk=1, row h=1,
and kr+h row=identity follow in the original structure-module endomorphism
ring. Commutativity of that ring is proved on actual sections, including
zero rings and empty opens. No choice of coefficient field or alternate
module model occurs. These identities supply an actual local native
ShortComplex.Splitting with the stated arrows.

The original over-site/open-scheme comparison transports the local
splittings. Native shortExact_of_restrict_openCover then proves the
original sequence short exact. The generic projective Koszul and Euler
complexes have different native terms and arrows and are not substituted
for this sequence. No ProjectiveSpace import or duplicate construction of
generating section frames is needed.
