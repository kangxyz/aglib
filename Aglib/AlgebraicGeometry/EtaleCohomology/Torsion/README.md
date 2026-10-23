# Torsion on the small-etale site

This family specializes the generic [site torsion construction](../../../CategoryTheory/Sites/Torsion/README.md)
to the actual small-etale abelian sheaves `AbelianSheaf.{u,u+1} X`.

| Source | Scope |
| --- | --- |
| [Basic](Basic.lean) | Internal torsion, allowing different positive annihilators locally, is equivalent to torsion in every original geometric stalk. It uses the actual stalk family and needs no Ext or finite-type premise. |
| [Colimit](Colimit.lean) | Every internally torsion abelian etale sheaf is the actual filtered colimit of its native factorial annihilator kernels, through their original inclusions. |

The colimit presentation is a sheaf-theoretic source for bounded-torsion
devissage. It does not prove cohomological filtered-colimit continuity,
constructibility, finite cogeneration, the local proper-base-change criterion,
or proper base change.
