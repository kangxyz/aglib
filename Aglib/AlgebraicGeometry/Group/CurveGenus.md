# Native coherent genus of group curves

`Aglib.AlgebraicGeometry.Group.CurveGenus` proves
`AlgebraicGeometry.Scheme.Group.coherentGenus_eq_one`:
for a field `k`, `G : Grp (FScheme k)`, and `Curve.Properties G.X`, the native
`Curve.coherentGenus k G.X` equals `1`. The curve properties are smooth relative
dimension one, properness, and geometric connectedness. There is no genus,
representability, or theorem-family input.

The genus-independent difference-map identity proves that the actual diagonal
conormal line bundle has zero Picard class. The canonical diagonal-conormal
comparison identifies it with the native field differential sheaf, and the
native canonical-degree formula gives coherent genus one. The class-triviality
statement requires only smooth relative dimension one and separatedness.
`coherentGenus_eq_one_of_diagonalConormalIso` retains the earlier conditional
reduction as a reusable interface; the new theorem supplies its missing
geometric comparison internally.

The argument uses only the genus-independent identity/difference lemmas from
`Group.MultiplicationDegree`, the actual conormal comparison in
`Modules.Differentials.Diagonal`, and the native canonical-degree supplier. No
multiplication-degree theorem with a genus-one premise is used to prove genus.
