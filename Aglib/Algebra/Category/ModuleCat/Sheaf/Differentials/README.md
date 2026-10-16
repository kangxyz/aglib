# Actual relative differential sheaves

`Relative` applies the original module sheafification to the sole relative
differential presheaf from `ModuleCat.Differentials.Presheaf.Relative`.
In `SheafOfModulesOfCommRing.DifferentialsConstruction`, the resulting
`relativeDifferentials R φ` represents the native `Derivation φ` against
every actual module sheaf over `R`. The equivalence is exactly the original
sheafification Hom equivalence followed by the proved presheaf universal
equivalence. No quasicoherence condition is imposed on its target.

`derivation_d` identifies the universal differential with the original
`toSheafify` map applied to the original cokernel differential.
`desc_d`, `hom_ext`, `relativeDifferentialsHomEquiv_comp` and
`desc_postcomp` retain the original derivation values and coefficient maps.
For the identity functor, `relativeDifferentialsIdIso` is the original
sheafification functor applied to the native presheaf comparison; its forward
and inverse formulas preserve the same original sheafified `d a`.

Only the target category has a Grothendieck topology. The source and target
category object and morphism universes are independent of the coefficient
universe. The exact native weak sheafification, locally bijective criterion,
commutative-ring forgetting, and presheaf pullback-adjoint hypotheses are
retained. The two identity local-bijectivity properties are proved internally.
The arbitrary-scheme specialization uses the original structure map `f.c`
and the existing automatic presheaf pullback instance on scheme opens.
