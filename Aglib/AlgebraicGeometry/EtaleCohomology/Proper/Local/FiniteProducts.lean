/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.CoefficientTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.AnnihilatorProducts
public import Aglib.CategoryTheory.Preadditive.Annihilator.ProductReindex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Comparison
public import Aglib.Algebra.Homology.DerivedCategory.Ext.BiproductComparison
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Algebra.Category.Grp.Limits

/-! # Original cohomology tests on finite products of finite constant direct images

The existing finite-biproduct Ext comparison applies to the bicone of the
literal original product cone, retaining its point and projections. This
gives the original tests independently for injectivity and surjectivity,
including the empty product. The accepted kernel comparisons then give the
same tests on every actual n-annihilator and its genuine module target,
including moduli zero and one.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eX eS

attribute [local instance] hasSheafifyLarge

private theorem cohomologyFunctor_additive (X : Scheme.{u})
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)] (q : ℕ) :
    (cohomologyFunctor.{u, eX} X q).Additive := by
  change (CategoryTheory.Abelian.extFunctorObj _ q).Additive
  infer_instance

/-- The original additive cohomology functor preserves finite products.
The native additive-functor theorem supplies the comparison instances. -/
instance cohomologyFunctor_preservesFiniteProducts (X : Scheme.{u})
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)] (q : ℕ) :
    PreservesFiniteProducts (cohomologyFunctor.{u, eX} X q) := by
  let := cohomologyFunctor_additive X q
  exact Functor.preservesFiniteProductsOfAdditive _

section OriginalProducts

variable {X S : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
  (g : S ⟶ X) {k : ℕ} (F : Fin k → AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- Coordinatewise surjectivity gives surjectivity on the actual original
finite product coefficient. The parameter k may be zero. -/
theorem cohomologyPullback_surjective_finProduct
    (hF : ∀ i, Function.Surjective (cohomologyPullback.{u, eX, eS} g (F i) q)) :
    Function.Surjective (cohomologyPullback.{u, eX, eS} g (∏ᶜ F) q) := by
  let a := (((inverseImageConstantIso g).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
  change Function.Surjective ((inverseImage g).extPrecompMap a (∏ᶜ F) q)
  exact (inverseImage g).extPrecompMap_surjective_biproduct_on_image
    (𝟭 (AbelianSheaf.{u, u + 1} X)) a
    (biconeIsBilimitOfLimitConeOfIsLimit (productIsProduct F)) q hF

/-- Coordinatewise injectivity gives injectivity on the same original
product, independently of surjectivity and including the empty product. -/
theorem cohomologyPullback_injective_finProduct
    (hF : ∀ i, Function.Injective (cohomologyPullback.{u, eX, eS} g (F i) q)) :
    Function.Injective (cohomologyPullback.{u, eX, eS} g (∏ᶜ F) q) := by
  let a := (((inverseImageConstantIso g).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
  change Function.Injective ((inverseImage g).extPrecompMap a (∏ᶜ F) q)
  exact (inverseImage g).extPrecompMap_injective_biproduct_on_image
    (𝟭 (AbelianSheaf.{u, u + 1} X)) a
    (biconeIsBilimitOfLimitConeOfIsLimit (productIsProduct F)) q hF

end OriginalProducts

section OriginalFiniteIndices

variable {X S : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]

/-- The existing Ext comparison applies directly to the literal original
product on any finite index in the scheme universe. -/
theorem cohomologyPullback_surjective_finiteProduct
    (g : S ⟶ X) {ι : Type u} [Finite ι]
    (F : ι → AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : ∀ i, Function.Surjective (cohomologyPullback.{u, eX, eS} g (F i) q)) :
    Function.Surjective (cohomologyPullback.{u, eX, eS} g (∏ᶜ F) q) := by
  let := Fintype.ofFinite ι
  let a := (((inverseImageConstantIso g).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
  change Function.Surjective ((inverseImage g).extPrecompMap a (∏ᶜ F) q)
  exact (inverseImage g).extPrecompMap_surjective_biproduct_on_image
    (𝟭 (AbelianSheaf.{u, u + 1} X)) a
    (biconeIsBilimitOfLimitConeOfIsLimit (productIsProduct F)) q hF

/-- The same literal finite-index product has injective comparison whenever
each original component comparison is injective. -/
theorem cohomologyPullback_injective_finiteProduct
    (g : S ⟶ X) {ι : Type u} [Finite ι]
    (F : ι → AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : ∀ i, Function.Injective (cohomologyPullback.{u, eX, eS} g (F i) q)) :
    Function.Injective (cohomologyPullback.{u, eX, eS} g (∏ᶜ F) q) := by
  let := Fintype.ofFinite ι
  let a := (((inverseImageConstantIso g).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)
  change Function.Injective ((inverseImage g).extPrecompMap a (∏ᶜ F) q)
  exact (inverseImage g).extPrecompMap_injective_biproduct_on_image
    (𝟭 (AbelianSheaf.{u, u + 1} X)) a
    (biconeIsBilimitOfLimitConeOfIsLimit (productIsProduct F)) q hF

end OriginalFiniteIndices

namespace Proper

/-- The original-family scalar-kernel comparison for any finite index in the
scheme universe. Its value equals the original reindexed comparison. -/
def constantDirectImageProductAnnihilatorIsoFiniteIndex
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (n : ℕ)
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (A : ι → AddCommGrpCat.{u + 1}) :
    Sheaf.annihilator
        (∏ᶜ fun i => (directImage (f i)).obj
          ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))) n ≅
      ∏ᶜ fun i => (directImage (f i)).obj
        ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (kernel (n • 𝟙 (A i)))) := by
  let L : ι → AddCommGrpCat.{u + 1} ⥤ AbelianSheaf.{u, u + 1} X :=
    fun i => constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ directImage (f i)
  let (i : ι) : (L i).Additive := by
    change (constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      directImage (f i)).Additive
    infer_instance
  let (i : ι) : PreservesFiniteLimits (L i) := by
    let : PreservesFiniteLimits (constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      constantSheaf_preservesFiniteLimits (Y i)
    change PreservesFiniteLimits
      (constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ directImage (f i))
    exact Limits.comp_preservesFiniteLimits _ _
  exact Preadditive.nsmulKernelProductFunctorIso n L A

/-- The complete original Fin/reindex construction has exactly the new
original-index value, including both maps of the isomorphism. -/
private theorem constantDirectImageProductAnnihilatorIsoFiniteIndex_eq_originalReindex
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (n : ℕ)
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (A : ι → AddCommGrpCat.{u + 1}) :
    constantDirectImageProductAnnihilatorIsoFiniteIndex n Y f A =
      (by
        let := Fintype.ofFinite ι
        let E := (Fintype.equivFin ι).symm
        let F : ι → AbelianSheaf.{u, u + 1} X := fun i =>
          (directImage (f i)).obj
            ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))
        let K : ι → AbelianSheaf.{u, u + 1} X := fun i =>
          (directImage (f i)).obj
            ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (kernel (n • 𝟙 (A i))))
        let eP : (∏ᶜ (F ∘ E)) ≅ ∏ᶜ F := Pi.reindex E F
        let eAnn : Sheaf.annihilator (∏ᶜ (F ∘ E)) n ≅ Sheaf.annihilator (∏ᶜ F) n :=
          kernel.mapIso _ _ eP eP (by simp)
        let eFin : Sheaf.annihilator (∏ᶜ (F ∘ E)) n ≅ ∏ᶜ (K ∘ E) :=
          constantDirectImageProductAnnihilatorIso n (Y ∘ E) (fun j => f (E j)) (A ∘ E)
        exact eAnn.symm ≪≫ eFin ≪≫ Pi.reindex E K
      ) := by
  let L : ι → AddCommGrpCat.{u + 1} ⥤ AbelianSheaf.{u, u + 1} X :=
    fun i => constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ directImage (f i)
  let (i : ι) : (L i).Additive := by
    change (constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      directImage (f i)).Additive
    infer_instance
  let (i : ι) : PreservesFiniteLimits (L i) := by
    let : PreservesFiniteLimits (constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      constantSheaf_preservesFiniteLimits (Y i)
    change PreservesFiniteLimits
      (constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ directImage (f i))
    exact Limits.comp_preservesFiniteLimits _ _
  let := Fintype.ofFinite ι
  let E := (Fintype.equivFin ι).symm
  have h := Preadditive.nsmulKernelProductFunctorIso_eq_reindex n L A E
  simpa only [constantDirectImageProductAnnihilatorIsoFiniteIndex,
    constantDirectImageProductAnnihilatorIso, annihilatorProductIso,
    constantDirectImageAnnihilatorIso,
    AlgebraicGeometry.Scheme.EtaleCohomology.Proper.nsmulKernelIso,
    CategoryTheory.Functor.comp_obj, Function.comp_def,
    CategoryTheory.Sheaf.annihilator, L, E] using h

section StrictlyLocalProducts

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1}
    (pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)))]
  {ι : Type u} [Finite ι] (Y : ι → Scheme.{u})
  (f : ∀ i, Y i ⟶ ProjectiveLine.projectiveP1 R)
  [∀ i, IsFinite (f i)] (A : ι → AddCommGrpCat.{u + 1}) [∀ i, Finite (A i)]

/-- All-degree surjectivity for the finite product of the original finite
constant direct images, with finite values in universe u+1. -/
theorem finiteConstantDirectImageProduct_residuePullback_surjective
    [IsSepClosed (IsLocalRing.ResidueField R)] (q : ℕ) :
    Function.Surjective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (∏ᶜ fun i => (directImage (f i)).obj
        ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))) q) :=
  cohomologyPullback_surjective_finiteProduct _ _ q fun i =>
    finiteConstantDirectImage_residuePullback_surjective_of_finite_value (f i) (A i) q

/-- Degree-zero injectivity on those literal finite products requires no
separable-closure assumption on the residue field. -/
theorem finiteConstantDirectImageProduct_residuePullback_injective_zero :
    Function.Injective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (∏ᶜ fun i => (directImage (f i)).obj
        ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))) 0) :=
  cohomologyPullback_injective_finiteProduct _ _ 0 fun i =>
    finiteConstantDirectImage_residuePullback_injective_zero_of_finite_value (f i) (A i)

/-- Every actual n-annihilator of the original finite constant product has
the same all-degree surjectivity test, including n=0 and n=1. -/
theorem finiteConstantDirectImageProductAnnihilator_residuePullback_surjective
    [IsSepClosed (IsLocalRing.ResidueField R)] (n q : ℕ) :
    Function.Surjective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (Sheaf.annihilator (∏ᶜ fun i => (directImage (f i)).obj
        ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))) n) q) := by
  let B : ι → AddCommGrpCat.{u + 1} := fun i => kernel (n • 𝟙 (A i))
  have (i : ι) : Finite (B i) := finite_nsmulKernelValue n (A i)
  exact cohomologyPullback_surjective_of_iso _
    (constantDirectImageProductAnnihilatorIsoFiniteIndex n Y f A).symm q
    (finiteConstantDirectImageProduct_residuePullback_surjective Y f B q)

/-- Degree-zero injectivity transports to the same actual annihilator at
every modulus and every finite product size. -/
theorem finiteConstantDirectImageProductAnnihilator_residuePullback_injective_zero
    (n : ℕ) :
    Function.Injective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (Sheaf.annihilator (∏ᶜ fun i => (directImage (f i)).obj
        ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))) n) 0) := by
  let B : ι → AddCommGrpCat.{u + 1} := fun i => kernel (n • 𝟙 (A i))
  have (i : ι) : Finite (B i) := finite_nsmulKernelValue n (A i)
  exact cohomologyPullback_injective_of_iso _
    (constantDirectImageProductAnnihilatorIsoFiniteIndex n Y f A).symm 0
    (finiteConstantDirectImageProduct_residuePullback_injective_zero Y f B)

/-- The genuine n-annihilator target has the same original all-degree test
on its actual underlying abelian coefficient, for every modulus. -/
theorem finiteConstantDirectImageProductZModAnnihilator_residuePullback_surjective
    [IsSepClosed (IsLocalRing.ResidueField R)] (n q : ℕ) :
    Function.Surjective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj
        (zmodAnnihilator (ProjectiveLine.projectiveP1 R) n
          (∏ᶜ fun i => (directImage (f i)).obj
            ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))))) q) :=
  cohomologyPullback_surjective_of_iso _
    (zmodAnnihilatorUnderlyingIso (ProjectiveLine.projectiveP1 R) n _).symm q
    (finiteConstantDirectImageProductAnnihilator_residuePullback_surjective Y f A n q)

/-- The actual underlying genuine module target also has injective
degree-zero pullback, without a residue-field closure assumption. -/
theorem finiteConstantDirectImageProductZModAnnihilator_residuePullback_injective_zero
    (n : ℕ) :
    Function.Injective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj
        (zmodAnnihilator (ProjectiveLine.projectiveP1 R) n
          (∏ᶜ fun i => (directImage (f i)).obj
            ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))))) 0) :=
  cohomologyPullback_injective_of_iso _
    (zmodAnnihilatorUnderlyingIso (ProjectiveLine.projectiveP1 R) n _).symm 0
    (finiteConstantDirectImageProductAnnihilator_residuePullback_injective_zero Y f A n)

end StrictlyLocalProducts

section StrictlyLocalSmallProducts

variable {R : Type u} [CommRing R] [HenselianLocalRing R]
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 R))]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1}
    (pullback (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R)))]
  {ι : Type u} [Finite ι] (Y : ι → Scheme.{u})
  (f : ∀ i, Y i ⟶ ProjectiveLine.projectiveP1 R) [∀ i, IsFinite (f i)]
  (A : ι → AddCommGrpCat.{u}) [∀ i, Finite (A i)]

/-- The exact original family occurring in a finite constant product
embedding has surjective closed-fibre pullback in every degree. -/
theorem finiteConstantProduct_residuePullback_surjective
    [IsSepClosed (IsLocalRing.ResidueField R)] (q : ℕ) :
    Function.Surjective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (∏ᶜ fun i => (directImage (f i)).obj (ConstantFinite.coefficient (A i) (Y i))) q) :=
  finiteConstantDirectImageProduct_residuePullback_surjective Y f
    (fun i => ConstantFinite.value (A i)) q

/-- The same literal small-value finite product has injective degree-zero
comparison over every henselian local base. -/
theorem finiteConstantProduct_residuePullback_injective_zero :
    Function.Injective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (∏ᶜ fun i => (directImage (f i)).obj (ConstantFinite.coefficient (A i) (Y i))) 0) :=
  finiteConstantDirectImageProduct_residuePullback_injective_zero Y f
    (fun i => ConstantFinite.value (A i))

/-- The actual annihilator of the embedding's original product satisfies
all-degree surjectivity, at every modulus including zero and one. -/
theorem finiteConstantProductAnnihilator_residuePullback_surjective
    [IsSepClosed (IsLocalRing.ResidueField R)] (n q : ℕ) :
    Function.Surjective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (Sheaf.annihilator
        (∏ᶜ fun i => (directImage (f i)).obj (ConstantFinite.coefficient (A i) (Y i))) n) q) :=
  finiteConstantDirectImageProductAnnihilator_residuePullback_surjective Y f
    (fun i => ConstantFinite.value (A i)) n q

/-- The original small-value product annihilator has injective degree-zero
comparison at every modulus and every finite index. -/
theorem finiteConstantProductAnnihilator_residuePullback_injective_zero (n : ℕ) :
    Function.Injective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      (Sheaf.annihilator
        (∏ᶜ fun i => (directImage (f i)).obj (ConstantFinite.coefficient (A i) (Y i))) n) 0) :=
  finiteConstantDirectImageProductAnnihilator_residuePullback_injective_zero Y f
    (fun i => ConstantFinite.value (A i)) n

/-- The genuine target built from the original embedding product has the
required original underlying all-degree surjectivity test. -/
theorem finiteConstantProductZModAnnihilator_residuePullback_surjective
    [IsSepClosed (IsLocalRing.ResidueField R)] (n q : ℕ) :
    Function.Surjective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj
        (zmodAnnihilator (ProjectiveLine.projectiveP1 R) n
          (∏ᶜ fun i => (directImage (f i)).obj
            (ConstantFinite.coefficient (A i) (Y i))))) q) :=
  finiteConstantDirectImageProductZModAnnihilator_residuePullback_surjective Y f
    (fun i => ConstantFinite.value (A i)) n q

/-- Its actual genuine underlying target has injective degree-zero
comparison, without an extra residue-field hypothesis. -/
theorem finiteConstantProductZModAnnihilator_residuePullback_injective_zero (n : ℕ) :
    Function.Injective (cohomologyPullback.{u, eX, eS}
      (pullback.fst (ProjectiveLine.structureMap R) (LocalRing.residueSpecMap R))
      ((Reduction.zmodUnderlying (ProjectiveLine.projectiveP1 R) n).obj
        (zmodAnnihilator (ProjectiveLine.projectiveP1 R) n
          (∏ᶜ fun i => (directImage (f i)).obj
            (ConstantFinite.coefficient (A i) (Y i))))) 0) :=
  finiteConstantDirectImageProductZModAnnihilator_residuePullback_injective_zero Y f
    (fun i => ConstantFinite.value (A i)) n

end StrictlyLocalSmallProducts

end Proper

end AlgebraicGeometry.Scheme.EtaleCohomology
