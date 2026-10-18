# Cartesian torsor actions

`Basic` owns `CategoryTheory.TorsorAction`: the actual action record,
fibre equivalence, action map, universal kernel marking and their comparison.
The category is arbitrary cartesian monoidal. The conversion of an action to a
kernel marking retains its supplied pointed-lift rigidity hypothesis.

These constructions use Mathlib's `Grp` object and canonical cartesian maps.
Finite-etale pointed covers, marked-kernel base change and group monodromy are
current consumers; no scheme, curve or finiteness hypothesis is added to the
generic record.
