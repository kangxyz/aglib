# Larger-valued sheaf cohomology

| Source | Interface |
| --- | --- |
| [Basic](Basic.lean) | Original sheaf cohomology represented by the actual large-coefficient free representable and identified with the literal site `Sheaf.H`. |
| [Injectives](Injectives.lean) | Large-valued sheaf existence and injective suppliers used to discharge coefficient hypotheses. |

The comparison retains the original coefficient and restriction maps and the
ordinary-universe comparison. It is site-theoretic and makes no scheme or
proper-base-change claim. The concrete small-etale consumer is
[Slice/Etale](../Slice/Etale.lean).
