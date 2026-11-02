/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric.Composition
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.GeometricTop
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism

/-!
# Composition of the original global cohomology pullbacks

The existing whole-space open/constant comparison carries the original
open-cohomology composition law to the unchanged `Sheaf.H` map. Ordinary
adjunction composition identifies its actual coefficient arrow. The
structural and field-linear laws therefore apply to arbitrary scheme maps.
No flatness or exactness of geometric direct image is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (q : Z ⟶ Y)

/-- Whole composition of the original global additive-sheaf cohomology maps,
with the original composite inverse-image coefficient arrow. -/
theorem zariskiCohomologyMap_comp
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (C : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B)
    (b : (zariskiPullback q).obj B ⟶ C) (n : ℕ) :
    (zariskiCohomologyMap q B C b n).comp (zariskiCohomologyMap p A B a n) =
      zariskiCohomologyMap (q ≫ p) A C
        ((zariskiPullbackCompIso p q).inv.app A ≫ (zariskiPullback q).map a ≫ b) n := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨x, rfl⟩ := (sheafHPrimeTopAddEquiv X A n).surjective x
  have hx := ConcreteCategory.congr_hom
    (zariskiCohomologyOpenMap_comp_app p q A B C a b n (op ⊤)) x
  have h := congrArg (sheafHPrimeTopAddEquiv Z C n) hx
  change sheafHPrimeTopAddEquiv Z C n
      ((zariskiCohomologyOpenMap q B C b n).app (op ⊤)
        ((zariskiCohomologyOpenMap p A B a n).app (op ⊤) x)) =
    sheafHPrimeTopAddEquiv Z C n
      ((zariskiCohomologyOpenMap (q ≫ p) A C
        ((zariskiPullbackCompIso p q).inv.app A ≫ (zariskiPullback q).map a ≫ b) n).app
          (op ⊤) x) at h
  rw [sheafHPrimeTopAddEquiv_geometric, sheafHPrimeTopAddEquiv_geometric,
    sheafHPrimeTopAddEquiv_geometric] at h
  exact h


private theorem adjunction_comp_symm
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    {U : C} {V : D} {W : E} (f : U ⟶ R₁.obj V) (g : V ⟶ R₂.obj W) :
    ((a₁.comp a₂).homEquiv U W).symm (f ≫ R₁.map g) =
      L₂.map ((a₁.homEquiv U V).symm f) ≫ (a₂.homEquiv V W).symm g := by
  apply ((a₁.comp a₂).homEquiv U W).injective
  rw [Equiv.apply_symm_apply, Adjunction.comp_homEquiv]
  change f ≫ R₁.map g = a₁.homEquiv U (R₂.obj W)
    (a₂.homEquiv (L₁.obj U) W
      (L₂.map ((a₁.homEquiv U V).symm f) ≫ (a₂.homEquiv V W).symm g))
  rw [a₂.homEquiv_naturality_left, Equiv.apply_symm_apply,
    a₁.homEquiv_naturality_right, Equiv.apply_symm_apply]

private theorem adjunction_unique_symm
    {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} {R : D ⥤ C} (a₁ : F ⊣ R) (a₂ : G ⊣ R)
    {U : C} {V : D} (f : U ⟶ R.obj V) :
    (a₁.leftAdjointUniq a₂).inv.app U ≫ (a₁.homEquiv U V).symm f =
      (a₂.homEquiv U V).symm f := by
  apply (a₂.homEquiv U V).injective
  rw [a₂.homEquiv_naturality_right, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Equiv.apply_symm_apply]
  exact (a₁.homEquiv U V).apply_symm_apply f

private theorem adjunction_coefficient_comp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₀ : C ⥤ E} {R₀ : E ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₀ : L₀ ⊣ R₀)
    (e : R₂ ⋙ R₁ ≅ R₀) {U : C} {V : D} {W : E}
    (f : U ⟶ R₁.obj V) (g : V ⟶ R₂.obj W) :
    (((a₁.comp a₂).ofNatIsoRight e).leftAdjointUniq a₀).inv.app U ≫
        L₂.map ((a₁.homEquiv U V).symm f) ≫ (a₂.homEquiv V W).symm g =
      (a₀.homEquiv U W).symm ((f ≫ R₁.map g) ≫ e.hom.app W) := by
  have h : (((a₁.comp a₂).ofNatIsoRight e).homEquiv U W).symm
      ((f ≫ R₁.map g) ≫ e.hom.app W) =
        L₂.map ((a₁.homEquiv U V).symm f) ≫ (a₂.homEquiv V W).symm g := by
    rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    exact adjunction_comp_symm a₁ a₂ f g
  rw [← h]
  exact adjunction_unique_symm ((a₁.comp a₂).ofNatIsoRight e) a₀ _

/-- Transposing the original two direct-image coefficient maps gives the
actual composite inverse-image coefficient, through the native adjunction comparison. -/
theorem zariskiCoefficientPullback_comp
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (C : Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})
    (a : A ⟶ (zariskiPushforward p).obj B) (b : B ⟶ (zariskiPushforward q).obj C) :
    (zariskiPullbackCompIso p q).inv.app A ≫
        (zariskiPullback q).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base).homEquiv
            A B).symm a) ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} q.base).homEquiv
          B C).symm b =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (q ≫ p).base).homEquiv
        A C).symm (a ≫ (zariskiPushforward p).map b) := by
  have h := adjunction_coefficient_comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} q.base)
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (q.base ≫ p.base))
    (TopCat.Sheaf.abelianPushforwardCompIso p.base q.base) a b
  have hi : (a ≫ (zariskiPushforward p).map b) ≫
      (TopCat.Sheaf.abelianPushforwardCompIso p.base q.base).hom.app C =
        a ≫ (zariskiPushforward p).map b := Category.comp_id _
  rw [hi] at h
  exact h

/-- Actual structural direct-image coefficient maps compose by the original scheme maps. -/
theorem structurePushforwardMap_comp :
    structurePushforwardMap (q ≫ p) =
      structurePushforwardMap p ≫ (zariskiPushforward p).map (structurePushforwardMap q) := by
  ext U x
  rfl

/-- The actual structural inverse-image coefficient is the native composite coefficient. -/
theorem structurePullbackMap_comp :
    (zariskiPullbackCompIso p q).inv.app (structureAddSheaf X) ≫
        (zariskiPullback q).map (structurePullbackMap p) ≫ structurePullbackMap q =
      structurePullbackMap (q ≫ p) := by
  rw [structurePullbackMap, structurePullbackMap, zariskiCoefficientPullback_comp,
    ← structurePushforwardMap_comp]
  rfl

/-- Composition on the original global structure-sheaf cohomology, for arbitrary maps. -/
theorem structureCohomologyPullback_comp (n : ℕ) :
    structureCohomologyPullback (q ≫ p) n =
      (structureCohomologyPullback q n).comp (structureCohomologyPullback p n) := by
  unfold structureCohomologyPullback
  rw [zariskiCohomologyMap_comp, structurePullbackMap_comp]

/-- The original identity structural direct-image arrow is the actual identity. -/
theorem structurePushforwardMap_id (X : Scheme.{u}) :
    structurePushforwardMap (𝟙 X) = 𝟙 (structureAddSheaf X) := by
  ext U x
  rfl

/-- The original identity pullback on structure-sheaf cohomology is the identity map. -/
theorem structureCohomologyPullback_id (X : Scheme.{u}) (n : ℕ) :
    structureCohomologyPullback (𝟙 X) n = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  apply (structureCohomologyPullback_bijective (𝟙 X) n).injective
  change (structureCohomologyPullback (𝟙 X) n)
      ((structureCohomologyPullback (𝟙 X) n) x) = (structureCohomologyPullback (𝟙 X) n) x
  have h := structureCohomologyPullback_comp (𝟙 X) (𝟙 X) n
  change structureCohomologyPullback (𝟙 X) n =
    (structureCohomologyPullback (𝟙 X) n).comp (structureCohomologyPullback (𝟙 X) n) at h
  exact DFunLike.congr_fun h.symm x

/-- The canonical inverse-image identity coefficient is the transpose of the actual identity. -/
def zariskiIdentityCoefficient (X : Scheme.{u})
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (zariskiPullback (𝟙 X)).obj A ⟶ A :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (𝟙 X : X ⟶ X).base).homEquiv A A).symm (𝟙 A)

/-- Identity on the whole original additive-sheaf global cohomology map. -/
theorem zariskiCohomologyMap_id (X : Scheme.{u})
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    zariskiCohomologyMap (𝟙 X) A A (zariskiIdentityCoefficient X A) n = AddMonoidHom.id _ := by
  have : IsIso (zariskiIdentityCoefficient X A) := by
    have : (TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (𝟙 X : X ⟶ X).base).IsEquivalence := zariskiPushforward_isEquivalence (𝟙 X)
    unfold zariskiIdentityCoefficient
    rw [Adjunction.homEquiv_counit]
    infer_instance
  have hc : (zariskiPullbackCompIso (𝟙 X) (𝟙 X)).inv.app A ≫
      (zariskiPullback (𝟙 X)).map (zariskiIdentityCoefficient X A) ≫
        zariskiIdentityCoefficient X A = zariskiIdentityCoefficient X A := by
    unfold zariskiIdentityCoefficient
    rw [zariskiCoefficientPullback_comp]
    erw [Category.id_comp ((zariskiPushforward (𝟙 X)).map (𝟙 A))]
    apply congrArg
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (𝟙 X : X ⟶ X).base).homEquiv A A).symm
    exact (zariskiPushforward (𝟙 X)).map_id A
  have h := zariskiCohomologyMap_comp (𝟙 X) (𝟙 X) A A A
    (zariskiIdentityCoefficient X A) (zariskiIdentityCoefficient X A) n
  rw [hc] at h
  change (zariskiCohomologyMap (𝟙 X) A A (zariskiIdentityCoefficient X A) n).comp
      (zariskiCohomologyMap (𝟙 X) A A (zariskiIdentityCoefficient X A) n) =
    zariskiCohomologyMap (𝟙 X) A A (zariskiIdentityCoefficient X A) n at h
  apply AddMonoidHom.ext
  intro x
  apply (zariskiCohomologyMap_bijective (𝟙 X) A A (zariskiIdentityCoefficient X A) n).injective
  change zariskiCohomologyMap (𝟙 X) A A (zariskiIdentityCoefficient X A) n
      (zariskiCohomologyMap (𝟙 X) A A (zariskiIdentityCoefficient X A) n x) =
    zariskiCohomologyMap (𝟙 X) A A (zariskiIdentityCoefficient X A) n x
  exact DFunLike.congr_fun h x

section Field

open AlgebraicGeometry.Scheme.OverField

variable {k : Type u} [Field k] {X Y Z : FScheme k}

/-- Whole composition for the existing original structural field-linear pullbacks. -/
theorem structureCohomologyPullbackLinear_comp (p : Y ⟶ X) (q : Z ⟶ Y) (n : ℕ) :
    structureCohomologyPullbackLinear (q ≫ p) n =
      (structureCohomologyPullbackLinear q n) ∘ₗ structureCohomologyPullbackLinear p n := by
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun (structureCohomologyPullback_comp p.left q.left n) x

/-- Identity for the same original structural field-linear pullback. -/
theorem structureCohomologyPullbackLinear_id (X : FScheme k) (n : ℕ) :
    structureCohomologyPullbackLinear (𝟙 X) n = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun (structureCohomologyPullback_id X.left n) x

end Field

end AlgebraicGeometry.Scheme.Cohomology
