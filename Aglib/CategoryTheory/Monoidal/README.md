# Monoidal categories

[Discrete](Discrete.lean), imported as `Aglib.CategoryTheory.Monoidal.Discrete`, extends Mathlib's `Mathlib.CategoryTheory.Monoidal.Discrete` in the native namespace `CategoryTheory.Discrete`. Mathlib braids `Discrete M` only for the multiplicative structure `Discrete.monoidal` of a commutative monoid; instance search selects the additive structure `Discrete.addMonoidal` on `Discrete ℤ`, which Mathlib does not braid. The leaf supplies the instances `Discrete.addBraidedCategory` (braiding `Discrete.eqToIso (add_comm _ _)`) and `Discrete.addSymmetricCategory` for every additive commutative monoid. It imports only Mathlib.

[UnitMultiplication](UnitMultiplication.lean), imported as `Aglib.CategoryTheory.Monoidal.UnitMultiplication`, works in the namespace `CategoryTheory`. For `σ : 𝟙_ C ⟶ A` in a monoidal category, `MonoidalCategory.unitMultiply σ F = (λ_ F).inv ≫ σ ▷ F : F ⟶ A ⊗ F` is natural in `F` (`unitMultiply_naturality`), is multiplication on the first factor of a tensor product followed by the associator (`unitMultiply_whiskerRight_associator`), and in a braided category commutes with a left factor up to the braiding (`whiskerLeft_unitMultiply`). For a lax monoidal functor `F` and `σ : 𝟙_ D ⟶ F.obj X`, `Functor.LaxMonoidal.unitMultiply_μ_whiskerRight` compares multiplication on an outer tensor factor with the tensorator, and, for a lax braided functor, `Functor.LaxBraided.whiskerLeft_unitMultiply_μ` does so on an inner factor, with the image of the braiding of `X` past the outer object. The proofs are rewriting chains of associator and unitor naturality, `whisker_exchange`, the associativity of `μ` and its braiding compatibility. It imports only Mathlib.

The first consumer is the braided twisting functor of polynomial projective space ([ProjectiveSpace/Tensor/Monoidal](../../AlgebraicGeometry/ProjectiveSpace/Tensor/Monoidal/README.md)). Its focused tests guard these declarations: [AglibTest Functor](../../../AglibTest/AlgebraicGeometry/ProjectiveSpace/Tensor/Monoidal/Functor.lean) the two `Discrete` instances, and [AglibTest Multiplication](../../../AglibTest/AlgebraicGeometry/ProjectiveSpace/Tensor/Monoidal/Multiplication.lean) the `unitMultiply` lemmas.

[Untwist](Untwist.lean), imported as `Aglib.CategoryTheory.Monoidal.Untwist`: for an invertible
pairing `P : L ⊗ L' ≅ 𝟙_ C`, `MonoidalCategory.untwistIso P I : (L ⊗ I) ⊗ L' ≅ I` and its
composition formula `untwistIso_hom_comp`, its naturality (`untwistIso_hom_naturality`) and its
value at the unit (`rightUnitor_inv_whiskerRight_untwistIso_hom`).
[UntwistVanishing](UntwistVanishing.lean) (`C` preadditive, tensor additive): faithfulness of `- ▷ L'` on zero morphisms (`eq_zero_of_whiskerRight_eq_zero`) and
`comp_rightUnitor_inv_whiskerLeft_eq_zero`. Consumer: the twisted ideal sheaf of a Hilbert family
([HilbertScheme/IdealTwist/Untwist](../../AlgebraicGeometry/HilbertScheme/IdealTwist/Untwist.lean),
[HilbertScheme/PulledBackGrassmannianPoint](../../AlgebraicGeometry/HilbertScheme/PulledBackGrassmannianPoint.lean)).

[GrpObjOfMono](GrpObjOfMono.lean), imported as `Aglib.CategoryTheory.Monoidal.GrpObjOfMono`, works
in the namespace `CategoryTheory`. A monomorphism `j : H ⟶ G` into a monoid object, through which
the unit and `(j ⊗ₘ j) ≫ μ[G]` factor, makes `H` a monoid object (`MonObj.ofMono`) with `j` a monoid
morphism (`MonObj.isMonHom_ofMono`). In a cartesian monoidal category, if `G` is a group object and
`j ≫ ι[G]` factors too, `GrpObj.ofMono` and `GrpObj.isMonHom_ofMono` give the group object. Each
axiom of `H` is that of `G` after cancelling `j`. It imports only Mathlib. Consumer:
[Group/IdentityComponent/Basic](../../AlgebraicGeometry/Group/IdentityComponent/Basic.lean).
`CategoryTheory.monObjOfJointDetection`
([JointDetection](../../AlgebraicGeometry/GrothendieckExistence/Algebraization/JointDetection.lean))
treats jointly detecting families; `MonObj.ofMono` is its one-element case.

[AdjunctionHomMulEquiv](AdjunctionHomMulEquiv.lean), imported as
`Aglib.CategoryTheory.Monoidal.AdjunctionHomMulEquiv`: for cartesian monoidal `C`, `D`, an
adjunction `adj : L ⊣ R` with `R` monoidal and a monoid object `M` of `D`, the adjunction bijection
is an isomorphism of monoids `adj.homMulEquiv T : (L T ⟶ M) ≃* (T ⟶ R M)` for the monoid object
`R.obj M` of Mathlib's `Functor.monObjObj` (`Adjunction.homEquiv_mul`, `Adjunction.homEquiv_one`,
`Adjunction.homEquiv_symm_mul`). It imports only Mathlib. Consumer:
[Picard/BaseChangeGroupLaw](../../AlgebraicGeometry/Picard/BaseChangeGroupLaw.lean).

[GrpObjShear](GrpObjShear.lean), imported as `Aglib.CategoryTheory.Monoidal.GrpObjShear`, works in
the namespace `CategoryTheory.GrpObj`. For a group object `G` of a cartesian monoidal category,
`GrpObj.shearIso G : G ⊗ G ≅ G ⊗ G` is `(a, b) ↦ (a b⁻¹, b)` with inverse `(c, b) ↦ (c b, b)`, in
the group structure on morphisms into `G`; `shearIso_hom_fst` identifies its first coordinate with
the division map `fst G G / snd G G`, and `shearIso_hom_snd` keeps the second (the diagram of Stacks
047K). It imports only Mathlib. Consumer:
[Group/IdentityComponent/QuasiCompact](../../AlgebraicGeometry/Group/IdentityComponent/QuasiCompact.lean).
