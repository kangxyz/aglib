# Detection by the actual small acyclic family

This family assembles the proved exhaustive source filtration with native
Hom-complex exactness and entire-predecessor inverse-limit acyclicity.
The tests are the single final shift-closed family used by replacement map
killing, not a separately assumed detecting collection.

- [Tests](Tests.lean) transports nullhomotopies through the explicit shift
  isomorphisms and applies all-degree source-shift detection. It does not
  infer Hom-complex acyclicity merely from degree-zero vanishing.
- [Stages](Stages.lean) proves Hom-complex acyclicity by actual transfinite
  source-stage induction. It aligns the original entire-predecessor comparison,
  uses the actual successor cokernel sequence, and transports the limit result
  through the native stage colimit isomorphism.
- [Basic](Basic.lean) applies the entire-prefix theorem to the actual exhaustive
  filtration and transports along its original colimit isomorphism. Native
  degree-zero boundaries then give homotopies and `CochainComplex.IsKInjective`.
  Thus the small detecting property is a theorem, not a new assumption.
