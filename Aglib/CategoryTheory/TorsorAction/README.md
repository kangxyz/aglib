# Cartesian torsor actions

`Basic` owns `CategoryTheory.TorsorAction`: the actual action record,
fibre equivalence, action map, universal kernel marking and their comparison.
The category is arbitrary cartesian monoidal. The conversion of an action to a
kernel marking retains its supplied pointed-lift rigidity hypothesis.

These constructions use Mathlib's `Grp` object and canonical cartesian maps.
Finite-etale pointed covers, marked-kernel base change and group monodromy are
current consumers; no scheme, curve or finiteness hypothesis is added to the
generic record.

[KernelMarkingOrbits](KernelMarkingOrbits.lean) extends the existing `CategoryTheory.KernelMarking` object.
Its universally constructed comparison is an actual group-object automorphism;
re-marking gives a free transitive automorphism action whenever a marking exists.
[TransportMarking](TransportMarking.lean) transports the same universal marking along a supplied
commuting source-group isomorphism. The all-test-object kernel property remains
the input; no scheme, elliptic kernel or isogeny classification is assumed.
