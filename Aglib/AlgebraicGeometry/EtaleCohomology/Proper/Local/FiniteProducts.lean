/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.CoefficientTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.AnnihilatorProducts
public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Comparison
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Algebra.Category.Grp.Limits

/-! # Original cohomology tests on finite products of finite constant direct images

Finite-product preservation of the original additive cohomology functors
gives coordinate equivalences on both sides of original inverse image.
The original projection naturality equations give coordinatewise lifting
and equality, including the empty product. The accepted kernel comparisons
then give the same tests on every actual n-annihilator and its genuine
module target, including moduli zero and one.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eX eS c v e

attribute [local instance] hasSheafifyLarge

section FiniteProductCoordinates

variable {C : Type c} [Category.{v} C] [HasFiniteProducts C]
  (F : C ⥤ AddCommGrpCat.{e}) [PreservesFiniteProducts F]
  {k : ℕ} (D : Fin k → C)

/-- The canonical finite-product comparison followed by the native
type-valued product identification gives the actual coordinate equivalence. -/
def functorFiniteProductEquiv :
    F.obj (∏ᶜ D) ≃ ∀ i, F.obj (D i) :=
  ((PreservesProduct.iso (F ⋙ CategoryTheory.forget AddCommGrpCat) D) ≪≫
    Types.productIso (fun i => (F.obj (D i) : Type e))).toEquiv

private theorem functorFiniteProductEquiv_apply
    (x : F.obj (∏ᶜ D)) (i : Fin k) :
    functorFiniteProductEquiv F D x i = F.map (Pi.π D i) x := by
  change (Types.productIso (fun i => (F.obj (D i) : Type e))).hom
      ((PreservesProduct.iso (F ⋙ CategoryTheory.forget AddCommGrpCat) D).hom x) i = _
  rw [Types.productIso_hom_comp_eval_apply, PreservesProduct.iso_hom]
  exact ConcreteCategory.congr_hom
    (piComparison_comp_π (F ⋙ CategoryTheory.forget AddCommGrpCat) D i) x

end FiniteProductCoordinates

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

/-- Finite products in the original coefficient variable give the actual
cohomology coordinate equivalence, with no value-universe resizing. -/
def cohomologyFiniteProductEquiv :
    Sheaf.H.{eX} (∏ᶜ F) q ≃ ∀ i, Sheaf.H.{eX} (F i) q :=
  functorFiniteProductEquiv (cohomologyFunctor.{u, eX} X q) F

/-- The target equivalence uses the original inverse-image functor itself. -/
def inverseImageCohomologyFiniteProductEquiv :
    Sheaf.H.{eS} ((inverseImage g).obj (∏ᶜ F)) q ≃
      ∀ i, Sheaf.H.{eS} ((inverseImage g).obj (F i)) q :=
  functorFiniteProductEquiv (inverseImage g ⋙ cohomologyFunctor.{u, eS} S q) F

/-- Source coordinates are the original cohomology maps of the original
product projections. -/
theorem cohomologyFiniteProductEquiv_apply
    (x : Sheaf.H.{eX} (∏ᶜ F) q) (i : Fin k) :
    cohomologyFiniteProductEquiv F q x i = Sheaf.H.map (Pi.π F i) q x :=
  functorFiniteProductEquiv_apply (cohomologyFunctor.{u, eX} X q) F x i

omit [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)] in
/-- Target coordinates retain the original inverse images of those same
product projections. -/
theorem inverseImageCohomologyFiniteProductEquiv_apply
    (x : Sheaf.H.{eS} ((inverseImage g).obj (∏ᶜ F)) q) (i : Fin k) :
    inverseImageCohomologyFiniteProductEquiv g F q x i =
      Sheaf.H.map ((inverseImage g).map (Pi.π F i)) q x :=
  functorFiniteProductEquiv_apply
    (inverseImage g ⋙ cohomologyFunctor.{u, eS} S q) F x i

/-- Coordinatewise surjectivity gives surjectivity on the actual original
finite product coefficient. The parameter k may be zero. -/
theorem cohomologyPullback_surjective_finProduct
    (hF : ∀ i, Function.Surjective (cohomologyPullback.{u, eX, eS} g (F i) q)) :
    Function.Surjective (cohomologyPullback.{u, eX, eS} g (∏ᶜ F) q) := by
  intro z
  let t := inverseImageCohomologyFiniteProductEquiv g F q z
  choose x hx using fun i => hF i (t i)
  let a := (cohomologyFiniteProductEquiv F q).symm x
  refine ⟨a, (inverseImageCohomologyFiniteProductEquiv g F q).injective ?_⟩
  funext i
  rw [inverseImageCohomologyFiniteProductEquiv_apply]
  rw [← cohomologyPullback_coefficientMap]
  have hcoord : Sheaf.H.map (Pi.π F i) q a = x i := by
    rw [← cohomologyFiniteProductEquiv_apply]
    exact congrFun ((cohomologyFiniteProductEquiv F q).apply_symm_apply x) i
  rw [hcoord]
  exact hx i

/-- Coordinatewise injectivity gives injectivity on the same original
product, independently of surjectivity and including the empty product. -/
theorem cohomologyPullback_injective_finProduct
    (hF : ∀ i, Function.Injective (cohomologyPullback.{u, eX, eS} g (F i) q)) :
    Function.Injective (cohomologyPullback.{u, eX, eS} g (∏ᶜ F) q) := by
  intro a b hab
  apply (cohomologyFiniteProductEquiv F q).injective
  funext i
  rw [cohomologyFiniteProductEquiv_apply, cohomologyFiniteProductEquiv_apply]
  apply hF i
  rw [cohomologyPullback_coefficientMap, cohomologyPullback_coefficientMap, hab]

end OriginalProducts

section OriginalFiniteIndices

variable {X S : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]

/-- Native product reindexing transports the finite-coordinate test back
to the literal original product on any finite index in the scheme universe. -/
theorem cohomologyPullback_surjective_finiteProduct
    (g : S ⟶ X) {ι : Type u} [Finite ι]
    (F : ι → AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : ∀ i, Function.Surjective (cohomologyPullback.{u, eX, eS} g (F i) q)) :
    Function.Surjective (cohomologyPullback.{u, eX, eS} g (∏ᶜ F) q) := by
  let := Fintype.ofFinite ι
  let E := (Fintype.equivFin ι).symm
  exact cohomologyPullback_surjective_of_iso g (Pi.reindex E F) q
    (cohomologyPullback_surjective_finProduct g (F ∘ E) q (fun j => hF (E j)))

/-- Injectivity returns to the same original finite-index product through
the canonical reindex isomorphism. -/
theorem cohomologyPullback_injective_finiteProduct
    (g : S ⟶ X) {ι : Type u} [Finite ι]
    (F : ι → AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hF : ∀ i, Function.Injective (cohomologyPullback.{u, eX, eS} g (F i) q)) :
    Function.Injective (cohomologyPullback.{u, eX, eS} g (∏ᶜ F) q) := by
  let := Fintype.ofFinite ι
  let E := (Fintype.equivFin ι).symm
  exact cohomologyPullback_injective_of_iso g (Pi.reindex E F) q
    (cohomologyPullback_injective_finProduct g (F ∘ E) q (fun j => hF (E j)))

end OriginalFiniteIndices

namespace Proper

/-- The accepted finite-coordinate kernel comparison on the literal
original family indexed by any finite type in the scheme universe. Both
product transports are the native reindex maps. -/
def constantDirectImageProductAnnihilatorIso_finiteIndex
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (n : ℕ)
    (Y : ι → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (A : ι → AddCommGrpCat.{u + 1}) :
    Sheaf.annihilator
        (∏ᶜ fun i => (directImage (f i)).obj
          ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))) n ≅
      ∏ᶜ fun i => (directImage (f i)).obj
        ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (kernel (n • 𝟙 (A i)))) := by
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
    (constantDirectImageProductAnnihilatorIso_finiteIndex n Y f A).symm q
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
    (constantDirectImageProductAnnihilatorIso_finiteIndex n Y f A).symm 0
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
