# Classification under finite-etale base change

`GroupScheme` transports actual group objects in finite-etale covers.
`Classification` and `PointedClassification` compare the classification functor
and pointed fibre maps under the specified base change. Their native namespaces
are `Scheme.FiniteEtale.GroupBaseChange`, `ClassificationNaturality` and
`ClassificationNaturalityPointed`.

The canonical lower base-change functor and fibre equivalence are reused.
Generic classification retains its explicit GC/FF inputs; the closed-field and
connected-scheme supplier leaves have their own stronger hypotheses. The
chosen separably closed field-valued point, connectedness where required,
universes and exact comparison equations remain explicit. Current consumers are
fundamental-group and monodromy comparisons.
