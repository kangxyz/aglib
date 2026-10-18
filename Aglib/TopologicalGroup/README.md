# Split groups and pointed affine actions

`SplitExtension` owns `TopologicalGroup.SplitExtension`. It constructs kernel
conjugation, semidirect coordinates and their multiplication/inverse formulas.
The equivalences retain the actual splitting equation `p (s g) = g`;
topological conclusions retain their continuity and topological-group inputs.

`PointedAffineActions` constructs pointed affine permutation actions and their
continuous kernel characters, with actual section and geometric restriction
formulas. The finite continuous-action endpoint additionally retains its finite
discrete coefficient hypotheses. These interfaces feed continuous H1 split
coordinates and finite-etale monodromy.
