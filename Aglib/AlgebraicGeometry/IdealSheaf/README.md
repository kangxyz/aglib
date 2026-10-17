# Actual ideal modules and canonical comparisons

[Modules](Modules.lean), imported as `Aglib.AlgebraicGeometry.IdealSheaf.Modules`, defines `Scheme.Hom.idealModule i` as the actual kernel of the structure-module map `𝒪_X → i_*𝒪_D`. Its inclusion and sectionwise kernel equivalences retain the actual ring-section maps. This construction applies to arbitrary scheme morphisms; closed immersion is an additional premise on the results that need it.

[Affine](Affine.lean) compares spectral ideal modules with sheafification of the actual ring kernel and proves the stated finite-generation consequence of finite presentation. [Restriction](Restriction.lean) compares actual ideal restrictions and their inclusions. The [base-change family](BaseChange/README.md) constructs the canonical ideal pullback map and proves its quotient-flat isomorphism theorem.

[Descent](Descent/README.md) proves faithfully flat descent of closed subschemes (Nitsure, Lemma 6.7(2)) along flat, surjective, quasi-compact morphisms.

[Invertible/Affine](Invertible/Affine.lean) relates actual local ideal bases to regular principal generators. [Effective Cartier consequences](../EffectiveCartierDivisor/README.md) use local rank one of these actual ideals with their stated closed-immersion and smoothness hypotheses. No replacement ideal-sheaf predicate is introduced.
