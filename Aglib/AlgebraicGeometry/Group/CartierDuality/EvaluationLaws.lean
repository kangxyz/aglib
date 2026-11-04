/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Evaluation
public import Aglib.AlgebraicGeometry.Group.CartierDuality.SpecUnits.Naturality
public import Aglib.AlgebraicGeometry.Group.CartierDuality.UniversalProperty
public import Aglib.AlgebraicGeometry.Group.CartierDuality.Functor
public import Aglib.AlgebraicGeometry.Group.CartierDuality.Bidual
public import Aglib.LinearAlgebra.Coevaluation.Naturality

/-!
# Laws of the original finite Cartier evaluation

The evaluation morphism is the existing map represented by native coevaluation.
Its comparison with the same universal character uses the original product,
scalar-extension and Spec maps. Both separate group laws, group-map naturality
and the arbitrary native base-change character bijection use that same evaluation.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct Module.Dual.FiniteDual CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

local instance instBraidedAlgSpecEvaluationLaws (K : Type u) [CommRing K] :
    (AlgebraicGeometry.algSpec (CommRingCat.of K)).Braided :=
  AlgebraicGeometry.braidedAlgSpec

private theorem coevaluationUnit_naturality {k : Type u} [Field k]
    {A B : CommHopfAlgCat.{u} k} [Coalgebra.IsCocomm k A] [Coalgebra.IsCocomm k B]
    [FiniteDimensional k A] [FiniteDimensional k B] (f : A ⟶ B) :
    Units.map (Algebra.TensorProduct.map f.hom.toAlgHom
        (AlgHom.id k (Dual k A))).toMonoidHom (HopfAlgebra.coevaluationUnit k A) =
      Units.map (Algebra.TensorProduct.map (AlgHom.id k B)
        f.hom.dual.toAlgHom).toMonoidHom (HopfAlgebra.coevaluationUnit k B) := by
  apply Units.ext
  have h := TensorProduct.coevaluation_naturality_apply f.hom.toLinearMap 1
  change Algebra.TensorProduct.map f.hom.toAlgHom (AlgHom.id k (Dual k A))
      (coevaluation k A 1) =
    Algebra.TensorProduct.map (AlgHom.id k B) f.hom.dual.toAlgHom (coevaluation k B 1)
  have hf : f.hom.toAlgHom.toLinearMap = f.hom.toLinearMap := by
    ext a
    rfl
  have hd : f.hom.dual.toAlgHom.toLinearMap = f.hom.toLinearMap.dualMap := by
    ext g a
    rfl
  change TensorProduct.map f.hom.toAlgHom.toLinearMap LinearMap.id (coevaluation k A 1) =
    TensorProduct.map LinearMap.id f.hom.dual.toAlgHom.toLinearMap (coevaluation k B 1)
  rw [hf, hd]
  exact h

private theorem tensorSpec_naturality {k : Type u} [CommRing k]
    {A B C D : CommAlgCat.{u} k} (f : A ⟶ C) (g : B ⟶ D) :
    ((AlgebraicGeometry.algSpec (CommRingCat.of k)).map f.op ⊗ₘ
        (AlgebraicGeometry.algSpec (CommRingCat.of k)).map g.op) ≫
        (algSpecTensorIso A B).hom =
      (algSpecTensorIso C D).hom ≫
        (AlgebraicGeometry.algSpec (CommRingCat.of k)).map (f ⊗ₘ g).op := by
  exact Functor.LaxMonoidal.μ_natural _ f.op g.op

private theorem native_pairing_naturality {k : Type u} [Field k]
    {A B : CommHopfAlgCat.{u} k} [Coalgebra.IsCocomm k A] [Coalgebra.IsCocomm k B]
    [FiniteDimensional k A] [FiniteDimensional k B] (f : A ⟶ B) :
    ((AlgebraicGeometry.algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom f.hom.toAlgHom).op ⊗ₘ
        𝟙 ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj
          (op (CommAlgCat.of k (Dual k A))))) ≫
        (algSpecTensorIso (CommAlgCat.of k A) (CommAlgCat.of k (Dual k A))).hom ≫
        specUnitMap (CommAlgCat.of k A ⊗ CommAlgCat.of k (Dual k A))
          (HopfAlgebra.coevaluationUnit k A) =
      (𝟙 ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k B))) ⊗ₘ
        (AlgebraicGeometry.algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom f.hom.dual.toAlgHom).op) ≫
        (algSpecTensorIso (CommAlgCat.of k B) (CommAlgCat.of k (Dual k B))).hom ≫
        specUnitMap (CommAlgCat.of k B ⊗ CommAlgCat.of k (Dual k B))
          (HopfAlgebra.coevaluationUnit k B) := by
  have hl := tensorSpec_naturality (CommAlgCat.ofHom f.hom.toAlgHom)
    (𝟙 (CommAlgCat.of k (Dual k A)))
  have hr := tensorSpec_naturality (𝟙 (CommAlgCat.of k B))
    (CommAlgCat.ofHom f.hom.dual.toAlgHom)
  simp only [op_id] at hl hr
  rw [CategoryTheory.Functor.map_id] at hl hr
  rw [← Category.assoc, hl, Category.assoc]
  conv_rhs => rw [← Category.assoc, hr, Category.assoc]
  rw [specUnitMap_naturality, specUnitMap_naturality]
  exact congrArg (fun u =>
    (algSpecTensorIso (CommAlgCat.of k B) (CommAlgCat.of k (Dual k A))).hom ≫
      specUnitMap (CommAlgCat.of k B ⊗ CommAlgCat.of k (Dual k A)) u)
    (coevaluationUnit_naturality f)

private theorem pairing_transport_naturality {C : Type*} [Category C]
    [CartesianMonoidalCategory C] {X Y A B DA DB M : C}
    (eX : X ≅ A) (eY : Y ≅ B) (f : X ⟶ Y) (a : A ⟶ B) (d : DB ⟶ DA)
    (uA : A ⊗ DA ⟶ M) (uB : B ⊗ DB ⟶ M)
    (hf : eX.inv ≫ f ≫ eY.hom = a)
    (hu : (a ⊗ₘ 𝟙 DB) ≫ uB = (𝟙 A ⊗ₘ d) ≫ uA) :
    (f ⊗ₘ 𝟙 DB) ≫ (eY.hom ⊗ₘ 𝟙 DB) ≫ uB =
      (𝟙 X ⊗ₘ d) ≫ (eX.hom ⊗ₘ 𝟙 DA) ≫ uA := by
  apply (cancel_epi (eX.inv ⊗ₘ 𝟙 DB)).1
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    Category.comp_id, Iso.inv_hom_id]
  simpa only [Category.assoc, hf] using hu

private theorem comparison_inv_fst {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X A D Q : C} (t : A ⊗ D ≅ Q) (e : X ≅ A) :
    ((MonoidalCategory.tensorIso e (Iso.refl D)) ≪≫ t).inv ≫ fst X D =
      t.inv ≫ fst A D ≫ e.inv := by
  simp [Category.assoc]

private theorem comparison_inv_snd {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {X A D Q : C} (t : A ⊗ D ≅ Q) (e : X ≅ A) :
    ((MonoidalCategory.tensorIso e (Iso.refl D)) ≪≫ t).inv ≫ snd X D =
      t.inv ≫ snd A D := by
  simp [Category.assoc]

private theorem specTensor_inv_fst (K : Type u) [CommRing K]
    (A B : CommAlgCat.{u} K) :
    (algSpecTensorIso A B).inv.left ≫
        pullback.fst (Spec.algebraMap K A) (Spec.algebraMap K B) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom) := by
  change (pullbackSpecIso K A B).inv ≫ pullback.fst _ _ = _
  exact pullbackSpecIso_inv_fst K A B

private theorem specTensor_inv_snd (K : Type u) [CommRing K]
    (A B : CommAlgCat.{u} K) :
    (algSpecTensorIso A B).inv.left ≫
        pullback.snd (Spec.algebraMap K A) (Spec.algebraMap K B) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom) := by
  change (pullbackSpecIso K A B).inv ≫ pullback.snd _ _ = _
  exact pullbackSpecIso_inv_snd K A B

private theorem postcompose_eq {C : Type*} [Category C] {X Y Z W : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (d : X ⟶ Z) (c : Z ⟶ W) (h : a ≫ b = d) :
    a ≫ b ≫ c = d ≫ c := by
  rw [← Category.assoc, h]

private theorem specTensor_inv_fst_over (K : Type u) [CommRing K]
    (A B : CommAlgCat.{u} K) :
    (algSpecTensorIso A B).inv ≫
        fst ((algSpec (CommRingCat.of K)).obj (op A))
          ((algSpec (CommRingCat.of K)).obj (op B)) =
      (algSpec (CommRingCat.of K)).map (fst (op A) (op B)) := by
  change Functor.OplaxMonoidal.δ (algSpec (CommRingCat.of K)) (op A) (op B) ≫ _ = _
  exact Functor.OplaxMonoidal.δ_fst _ _ _

private theorem specTensor_inv_snd_over (K : Type u) [CommRing K]
    (A B : CommAlgCat.{u} K) :
    (algSpecTensorIso A B).inv ≫
        snd ((algSpec (CommRingCat.of K)).obj (op A))
          ((algSpec (CommRingCat.of K)).obj (op B)) =
      (algSpec (CommRingCat.of K)).map (snd (op A) (op B)) := by
  change Functor.OplaxMonoidal.δ (algSpec (CommRingCat.of K)) (op A) (op B) ≫ _ = _
  exact Functor.OplaxMonoidal.δ_snd _ _ _

private theorem specComparison_inv_fst (K : Type u) [CommRing K]
    (A B : CommAlgCat.{u} K) {X : Over (Spec (CommRingCat.of K))}
    (e : X ≅ (algSpec (CommRingCat.of K)).obj (op A)) :
    ((MonoidalCategory.tensorIso e
        (Iso.refl ((algSpec (CommRingCat.of K)).obj (op B)))) ≪≫
      algSpecTensorIso A B).inv ≫
        fst X ((algSpec (CommRingCat.of K)).obj (op B)) =
      (algSpec (CommRingCat.of K)).map (fst (op A) (op B)) ≫ e.inv := by
  have h0 := comparison_inv_fst (algSpecTensorIso A B) e
  have hs := specTensor_inv_fst_over K A B
  have hp := postcompose_eq _ _ _ e.inv hs
  exact h0.trans hp

private theorem specComparison_inv_snd (K : Type u) [CommRing K]
    (A B : CommAlgCat.{u} K) {X : Over (Spec (CommRingCat.of K))}
    (e : X ≅ (algSpec (CommRingCat.of K)).obj (op A)) :
    ((MonoidalCategory.tensorIso e
        (Iso.refl ((algSpec (CommRingCat.of K)).obj (op B)))) ≪≫
      algSpecTensorIso A B).inv ≫
        snd X ((algSpec (CommRingCat.of K)).obj (op B)) =
      (algSpec (CommRingCat.of K)).map (snd (op A) (op B)) := by
  have h0 := comparison_inv_snd (algSpecTensorIso A B) e
  have hs := specTensor_inv_snd_over K A B
  exact h0.trans hs

private theorem specComparison_inv_fst_scheme (K : Type u) [CommRing K]
    (A B : CommAlgCat.{u} K) {X : Over (Spec (CommRingCat.of K))}
    (e : X ≅ (algSpec (CommRingCat.of K)).obj (op A)) :
    ((MonoidalCategory.tensorIso e
        (Iso.refl ((algSpec (CommRingCat.of K)).obj (op B)))) ≪≫
      algSpecTensorIso A B).inv.left ≫
        pullback.fst X.hom (Spec.algebraMap K B) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom) ≫ e.inv.left := by
  have h0 := comparison_inv_fst (algSpecTensorIso A B) e
  have h := congrArg Over.Hom.left h0
  change ((MonoidalCategory.tensorIso e
        (Iso.refl ((algSpec (CommRingCat.of K)).obj (op B)))) ≪≫
      algSpecTensorIso A B).inv.left ≫ pullback.fst X.hom (Spec.algebraMap K B) =
    (algSpecTensorIso A B).inv.left ≫
      pullback.fst (Spec.algebraMap K A) (Spec.algebraMap K B) ≫ e.inv.left at h
  have hs := specTensor_inv_fst K A B
  have hp := postcompose_eq _ _ _ e.inv.left hs
  exact h.trans hp

private theorem specComparison_inv_snd_scheme (K : Type u) [CommRing K]
    (A B : CommAlgCat.{u} K) {X : Over (Spec (CommRingCat.of K))}
    (e : X ≅ (algSpec (CommRingCat.of K)).obj (op A)) :
    ((MonoidalCategory.tensorIso e
        (Iso.refl ((algSpec (CommRingCat.of K)).obj (op B)))) ≪≫
      algSpecTensorIso A B).inv.left ≫
        pullback.snd X.hom (Spec.algebraMap K B) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom) := by
  have h0 := comparison_inv_snd (algSpecTensorIso A B) e
  have h := congrArg Over.Hom.left h0
  change ((MonoidalCategory.tensorIso e
        (Iso.refl ((algSpec (CommRingCat.of K)).obj (op B)))) ≪≫
      algSpecTensorIso A B).inv.left ≫ pullback.snd X.hom (Spec.algebraMap K B) =
    (algSpecTensorIso A B).inv.left ≫
      pullback.snd (Spec.algebraMap K A) (Spec.algebraMap K B) at h
  exact h.trans (specTensor_inv_snd K A B)

private theorem original_unit_rectangle {K L : Type u} [CommRing K] [CommRing L]
    (A : CommAlgCat.{u} K) (B : CommAlgCat.{u} L) (Z : AlgebraicGeometry.Scheme.{u})
    (iA : Spec (CommRingCat.of A) ≅ Z) (iB : Spec (CommRingCat.of B) ≅ Z)
    (f : A →+* B) (u : Aˣ) (v : Bˣ)
    (c d : Z ⟶ AlgebraicGeometry.Scheme.Group.MultiplicativeGroup.affineScheme)
    (hA : iA.hom ≫ d = (specUnitMap A u).left ≫ prod.snd)
    (hB : iB.hom ≫ c = (specUnitMap B v).left ≫ prod.snd)
    (hRect : iB.hom = Spec.map (CommRingCat.ofHom f) ≫ iA.hom)
    (hUnit : Units.map f.toMonoidHom u = v) : c = d := by
  apply (cancel_epi iB.hom).mp
  have hn := specUnitMap_laurent_naturality A B f u
  have hu := congrArg
    (fun w : Bˣ => (show Spec (CommRingCat.of B) ⟶
        AlgebraicGeometry.Scheme.Group.MultiplicativeGroup.affineScheme.{u} from
      (specUnitMap B w).left ≫ prod.snd)) hUnit
  have h1 := hB.trans hu.symm
  have h2 := h1.trans hn.symm
  have h3 := congrArg (fun q => Spec.map (CommRingCat.ofHom f) ≫ q) hA.symm
  have h4 := postcompose_eq _ _ _ d hRect.symm
  exact h2.trans (h3.trans h4)

open AlgebraicGeometry.Scheme.OverField (FScheme Base)

private theorem coevaluationUnit_flip {k : Type u} [Field k]
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    Units.map (Algebra.TensorProduct.map (AlgHom.id k (Dual k A))
        (Module.Dual.evalAlgEquiv k A).symm.toAlgHom).toMonoidHom
        (HopfAlgebra.coevaluationUnit k (Dual k A)) =
      Units.map (Algebra.TensorProduct.comm k A (Dual k A)).toAlgHom.toMonoidHom
        (HopfAlgebra.coevaluationUnit k A) := by
  apply Units.ext
  change TensorProduct.map LinearMap.id
      (Module.Dual.evalAlgEquiv k A).symm.toAlgHom.toLinearMap
      (coevaluation k (Dual k A) 1) =
    TensorProduct.comm k A (Dual k A) (coevaluation k A 1)
  have he : (Module.Dual.evalAlgEquiv k A).symm.toAlgHom.toLinearMap ∘ₗ
      Module.Dual.eval k A = LinearMap.id := by
    ext a
    exact (Module.evalEquiv k A).symm_apply_apply a
  apply (TensorProduct.comm k (Dual k A) A).injective
  rw [← TensorProduct.map_comm, ← TensorProduct.coevaluation_flip,
    LinearMap.rTensor_def, TensorProduct.map_map, he]
  simp only [LinearMap.comp_id, TensorProduct.map_id, LinearMap.id_apply,
    TensorProduct.comm_comm]


/-- The original bidual algebra map evaluates the dual universal unit to the primal one. -/
private theorem secondCharacterUnit_eq {k : Type u} [Field k]
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    Units.map (Module.Dual.characterTensorHom k (Dual k A) A
        (Module.Dual.evalAlgEquiv k A).symm.toAlgHom).toMonoidHom
        (HopfAlgebra.coevaluationUnit k (Dual k A)) =
      HopfAlgebra.coevaluationUnit k A := by
  apply Units.ext
  change Module.Dual.characterTensorHom k (Dual k A) A
      (Module.Dual.evalAlgEquiv k A).symm.toAlgHom (coevaluation k (Dual k A) 1) =
    coevaluation k A 1
  rw [Module.Dual.characterTensorHom_apply]
  have h := congrArg
    (fun u : (Dual k A ⊗[k] A)ˣ =>
      Algebra.TensorProduct.comm k (Dual k A) A (u : Dual k A ⊗[k] A))
    (coevaluationUnit_flip A)
  change TensorProduct.comm k (Dual k A) A
      (TensorProduct.map LinearMap.id
        (Module.Dual.evalAlgEquiv k A).symm.toAlgHom.toLinearMap
        (coevaluation k (Dual k A) 1)) =
    TensorProduct.comm k (Dual k A) A
      (TensorProduct.comm k A (Dual k A) (coevaluation k A 1)) at h
  rw [← TensorProduct.map_comm, TensorProduct.comm_comm] at h
  simpa only [LinearMap.lTensor_def, ← TensorProduct.map_comm] using h

private theorem tensorSpec_flip {k : Type u} [CommRing k]
    (A B : CommAlgCat.{u} k) :
    (β_ ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op A))
      ((AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op B))).hom ≫
        (algSpecTensorIso B A).hom =
      (algSpecTensorIso A B).hom ≫
        (AlgebraicGeometry.algSpec (CommRingCat.of k)).map
          (CommAlgCat.ofHom (Algebra.TensorProduct.comm k B A).toAlgHom).op := by
  exact (Functor.LaxBraided.braided (F := AlgebraicGeometry.algSpec (CommRingCat.of k))
    (op A) (op B)).symm

private theorem tensor_transpose_comparison {C : Type*} [Category C]
    [MonoidalCategory C] [BraidedCategory C] {X Y A D : C}
    (e : X ≅ A) (f : Y ≅ D) :
    (𝟙 Y ⊗ₘ e.inv) ≫ (β_ Y X).hom ≫ (e.hom ⊗ₘ f.hom) =
      (f.hom ⊗ₘ 𝟙 A) ≫ (β_ D A).hom := by
  rw [← BraidedCategory.braiding_naturality f.hom e.hom]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Iso.inv_hom_id]

private theorem product_transpose_rectangle (K : Type u) [CommRing K]
    (A D : CommAlgCat.{u} K) {X Y : Over (Spec (CommRingCat.of K))}
    (e : X ≅ (algSpec (CommRingCat.of K)).obj (op A))
    (f : Y ≅ (algSpec (CommRingCat.of K)).obj (op D)) :
    let P := MonoidalCategory.tensorIso e f ≪≫ algSpecTensorIso A D
    let Q := MonoidalCategory.tensorIso f
        (Iso.refl ((algSpec (CommRingCat.of K)).obj (op A))) ≪≫ algSpecTensorIso D A
    Q.inv ≫ (𝟙 Y ⊗ₘ e.inv) ≫ (β_ Y X).hom ≫ P.hom =
      (algSpec (CommRingCat.of K)).map
        (CommAlgCat.ofHom (Algebra.TensorProduct.comm K A D).toAlgHom).op := by
  dsimp only
  let P := MonoidalCategory.tensorIso e f ≪≫ algSpecTensorIso A D
  let Q := MonoidalCategory.tensorIso f
      (Iso.refl ((algSpec (CommRingCat.of K)).obj (op A))) ≪≫ algSpecTensorIso D A
  change Q.inv ≫ (𝟙 Y ⊗ₘ e.inv) ≫ (β_ Y X).hom ≫ P.hom = _
  apply (cancel_epi Q.hom).1
  rw [Iso.hom_inv_id_assoc]
  have h1 := congrArg (fun q => q ≫ (algSpecTensorIso A D).hom)
    (tensor_transpose_comparison e f)
  have h2 := congrArg (fun q => (f.hom ⊗ₘ 𝟙 ((algSpec (CommRingCat.of K)).obj (op A))) ≫ q)
    (tensorSpec_flip D A)
  simp only [Category.assoc] at h1 h2
  have hh := h1.trans h2
  dsimp only [P, Q, Iso.trans_hom, MonoidalCategory.tensorIso_hom, Iso.refl_hom]
  simpa only [Category.assoc] using hh

private theorem unit_product_transpose (K : Type u) [CommRing K]
    (A D : CommAlgCat.{u} K) {X Y : Over (Spec (CommRingCat.of K))}
    (e : X ≅ (algSpec (CommRingCat.of K)).obj (op A))
    (f : Y ≅ (algSpec (CommRingCat.of K)).obj (op D))
    (u : ((A ⊗ D : CommAlgCat.{u} K))ˣ) :
    let P := MonoidalCategory.tensorIso e f ≪≫ algSpecTensorIso A D
    let Q := MonoidalCategory.tensorIso f
        (Iso.refl ((algSpec (CommRingCat.of K)).obj (op A))) ≪≫ algSpecTensorIso D A
    Q.hom ≫ specUnitMap (D ⊗ A)
        (Units.map (Algebra.TensorProduct.comm K A D).toAlgHom.toMonoidHom u) =
      (𝟙 Y ⊗ₘ e.inv) ≫ (β_ Y X).hom ≫ P.hom ≫ specUnitMap (A ⊗ D) u := by
  dsimp only
  let P := MonoidalCategory.tensorIso e f ≪≫ algSpecTensorIso A D
  let Q := MonoidalCategory.tensorIso f
      (Iso.refl ((algSpec (CommRingCat.of K)).obj (op A))) ≪≫ algSpecTensorIso D A
  let w := Units.map (Algebra.TensorProduct.comm K A D).toAlgHom.toMonoidHom u
  change Q.hom ≫ specUnitMap (D ⊗ A) w =
    (𝟙 Y ⊗ₘ e.inv) ≫ (β_ Y X).hom ≫ P.hom ≫ specUnitMap (A ⊗ D) u
  apply (cancel_epi Q.inv).1
  have hL := Iso.inv_hom_id_assoc Q (specUnitMap (D ⊗ A) w)
  have hR0 := product_transpose_rectangle K A D e f
  have hR1 := congrArg (fun q => q ≫ specUnitMap (A ⊗ D) u) hR0
  simp only [Category.assoc] at hR1
  have hR2 := specUnitMap_naturality
    (CommAlgCat.ofHom (Algebra.TensorProduct.comm K A D).toAlgHom) u
  have hR := hR1.trans hR2
  exact hL.trans hR.symm

private theorem groupPullbackBaseMap_tensor {k : Type u} [Field k]
    (H : Grp (FScheme k)) {T U : FScheme k} (h : U ⟶ T) :
    groupPullbackBaseMap H h = (𝟙 H.X ⊗ₘ h).left := rfl

private theorem functor_tensor_inverse_cancel {C E : Type*} [Category C] [Category E]
    [MonoidalCategory C] (F : C ⥤ E) (Y : C) {X A M : C}
    (e : X ≅ A) (v : Y ⊗ X ⟶ M) :
    F.map (𝟙 Y ⊗ₘ e.hom) ≫ F.map ((𝟙 Y ⊗ₘ e.inv) ≫ v) = F.map v := by
  rw [← CategoryTheory.Functor.map_comp, ← Category.assoc,
    tensorHom_comp_tensorHom, Category.id_comp, Iso.hom_inv_id,
    id_tensorHom_id, Category.id_comp]


private theorem mapIso_refl_trans_inv_comp {C E : Type*} [Category C] [Category E]
    (F : C ⥤ E) (X : C) {Y Z : E} (S : F.obj X ≅ Y) (m : F.obj X ⟶ Z) :
    (F.mapIso (Iso.refl X).symm ≪≫ S).inv ≫ m = S.inv ≫ m := by
  simp only [Iso.refl_symm, CategoryTheory.Functor.mapIso_refl, Iso.refl_trans]

private theorem scalarCharacter_specUnitMap_second {k : Type u} [Field k]
    (D : CommHopfAlgCat.{u} k) [FiniteDimensional k D]
    (R : Type u) [CommRing R] [Algebra k R] (f : Dual k D →ₐ[k] R) :
    (scalarCharacterEquiv D R f).hom.hom =
      specUnitMap (CommAlgCat.of R (R ⊗[k] D))
        (Units.map (Module.Dual.characterTensorHom k D R f).toMonoidHom
          (HopfAlgebra.coevaluationUnit k D)) := by
  apply (specUnitsEquiv (CommAlgCat.of R (R ⊗[k] D))).injective
  rw [specUnitsEquiv_specUnitMap]
  exact scalarCharacterEquiv_coevaluation D R f




private theorem scalarComparison_inv_fst (k : Type u) [Field k]
    (A : CommHopfAlgCat.{u} k) (R : Type u) [CommRing R] [Algebra k R]
    (X : Grp (FScheme k)) (e : specGroup (k := k) A ≅ X) :
    ((Over.pullback (Spec.algebraMap k R)).mapGrp.mapIso e.symm ≪≫
        hopfSpecScalarExtensionIso k R A).inv.hom.hom.left ≫
        pullback.fst X.X.hom (Spec.algebraMap k R) =
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[k] R ⊗[k] A).toRingHom) ≫
        e.hom.hom.hom.left := by
  have hm := BaseChange.groupSchemeBaseChange_map_left_fst (Spec.algebraMap k R) e.hom
  have hs := hopfSpecScalarExtensionIso_inv_fst k R A
  dsimp only [BaseChange.groupSchemeBaseChange, specGroup, Functor.mapGrp_obj_X,
    Over.pullback_obj_left, Over.pullback_obj_hom] at hm
  have h1 := congrArg
    (fun q => (hopfSpecScalarExtensionIso k R A).inv.hom.hom.left ≫ q) hm
  have h2 := congrArg (fun q => q ≫ e.hom.hom.hom.left) hs
  exact h1.trans h2

private theorem scalarComparison_inv_snd (k : Type u) [Field k]
    (A : CommHopfAlgCat.{u} k) (R : Type u) [CommRing R] [Algebra k R]
    (X : Grp (FScheme k)) (e : specGroup (k := k) A ≅ X) :
    ((Over.pullback (Spec.algebraMap k R)).mapGrp.mapIso e.symm ≪≫
        hopfSpecScalarExtensionIso k R A).inv.hom.hom.left ≫
        pullback.snd X.X.hom (Spec.algebraMap k R) =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] A))) := by
  have hm := BaseChange.groupSchemeBaseChange_map_left_snd (Spec.algebraMap k R) e.hom
  have hs := hopfSpecScalarExtensionIso_inv_snd k R A
  dsimp only [BaseChange.groupSchemeBaseChange, specGroup, Functor.mapGrp_obj_X,
    Over.pullback_obj_left, Over.pullback_obj_hom] at hm
  have h1 := congrArg
    (fun q => (hopfSpecScalarExtensionIso k R A).inv.hom.hom.left ≫ q) hm
  exact h1.trans hs

private theorem spec_swap_fst (K R A : Type u)
    [CommRing K] [CommRing R] [CommRing A] [Algebra K R] [Algebra K A] :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm K A R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] R).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[K] R ⊗[K] A).toRingHom) := by
  rw [← Spec.map_comp]
  congr 1

private theorem spec_swap_snd (K R A : Type u)
    [CommRing K] [CommRing R] [CommRing A] [Algebra K R] [Algebra K A] :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm K A R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : R →ₐ[K] A ⊗[K] R).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[K] A))) := by
  rw [← Spec.map_comp]
  congr 1

private theorem inverse_projection_square {C : Type*} [Category C]
    {W V T Z : C} (s : W ⟶ T) (p : V ⟶ T) (a : W ⟶ V) (proj : T ⟶ Z)
    (i : W ⟶ Z) (j : V ⟶ Z)
    (hs : s ≫ proj = i) (hp : p ≫ proj = j) (ha : a ≫ j = i) :
    s ≫ proj = (a ≫ p) ≫ proj := by
  rw [hs, Category.assoc, hp, ha]

private theorem scalar_product_inverse_swap (k : Type u) [Field k]
    (A : CommHopfAlgCat.{u} k) (R : CommAlgCat.{u} k)
    (X : Grp (FScheme k)) (e : specGroup (k := k) A ≅ X) :
    let P := MonoidalCategory.tensorIso
        ((Grp.forget (FScheme k)).mapIso e.symm)
        (Iso.refl ((algSpec (CommRingCat.of k)).obj (op R))) ≪≫
      algSpecTensorIso (CommAlgCat.of k A) R
    let S := (Over.pullback (Spec.algebraMap k R)).mapGrp.mapIso e.symm ≪≫
      hopfSpecScalarExtensionIso k R A
    S.inv.hom.hom.left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm k A R).toRingHom) ≫
        P.inv.left := by
  dsimp only
  have hsf := scalarComparison_inv_fst k A R X e
  have hss := scalarComparison_inv_snd k A R X e
  have hpf := specComparison_inv_fst_scheme k (CommAlgCat.of k A) R
    ((Grp.forget (FScheme k)).mapIso e.symm)
  have hps := specComparison_inv_snd_scheme k (CommAlgCat.of k A) R
    ((Grp.forget (FScheme k)).mapIso e.symm)
  have hcf := spec_swap_fst k R A
  have hcs := spec_swap_snd k R A
  have hcfp := postcompose_eq _ _ _ e.hom.hom.hom.left hcf
  apply pullback.hom_ext
  · exact inverse_projection_square _ _ _ _ _ _ hsf hpf hcfp
  · exact inverse_projection_square _ _ _ _ _ _ hss hps hcs

private theorem native_evaluation_comparison (k : Type u) [Field k]
    (A : CommHopfAlgCat.{u} k) (R : CommAlgCat.{u} k)
    (X : Grp (FScheme k)) (e : specGroup (k := k) A ≅ X)
    (u : (((CommAlgCat.of k A) ⊗ R : CommAlgCat.{u} k))ˣ)
    (v : (CommAlgCat.of R (R ⊗[k] A))ˣ)
    (E : X.X ⊗ ((algSpec (CommRingCat.of k)).obj (op R)) ⟶
      MultiplicativeGroup.scheme (Base k))
    (U : ((Over.pullback (Spec.algebraMap k R)).mapGrp.obj X).X ⟶
      MultiplicativeGroup.scheme (Spec (CommRingCat.of R)))
    (hE : (MonoidalCategory.tensorIso
        ((Grp.forget (FScheme k)).mapIso e.symm)
        (Iso.refl ((algSpec (CommRingCat.of k)).obj (op R))) ≪≫
      algSpecTensorIso (CommAlgCat.of k A) R).inv ≫ E =
        specUnitMap ((CommAlgCat.of k A) ⊗ R) u)
    (hU : ((Over.pullback (Spec.algebraMap k R)).mapGrp.mapIso e.symm ≪≫
        hopfSpecScalarExtensionIso k R A).inv.hom.hom ≫ U =
      specUnitMap (CommAlgCat.of R (R ⊗[k] A)) v)
    (hUnit : Units.map (Algebra.TensorProduct.comm k A R).toRingHom.toMonoidHom u = v) :
    U.left ≫ prod.snd = E.left ≫ prod.snd := by
  let P := MonoidalCategory.tensorIso
      ((Grp.forget (FScheme k)).mapIso e.symm)
      (Iso.refl ((algSpec (CommRingCat.of k)).obj (op R))) ≪≫
    algSpecTensorIso (CommAlgCat.of k A) R
  let S := (Over.pullback (Spec.algebraMap k R)).mapGrp.mapIso e.symm ≪≫
    hopfSpecScalarExtensionIso k R A
  let Z : AlgebraicGeometry.Scheme.{u} :=
    (X.X ⊗ ((algSpec (CommRingCat.of k)).obj (op R))).left
  let EA : CommAlgCat.{u} k := (CommAlgCat.of k A) ⊗ R
  let SA := CommAlgCat.of R (R ⊗[k] A)
  let iA : Spec (CommRingCat.of EA) ≅ Z :=
    (Over.forget (Base k)).mapIso P.symm
  let iB : Spec (CommRingCat.of SA) ≅ Z :=
    (Grp.forget (Over (Spec (CommRingCat.of R))) ⋙
      Over.forget (Spec (CommRingCat.of R))).mapIso S.symm
  let piK : (MultiplicativeGroup.scheme (Base k)).left ⟶
      MultiplicativeGroup.affineScheme.{u} := prod.snd
  let piR : (MultiplicativeGroup.scheme (Spec (CommRingCat.of R))).left ⟶
      MultiplicativeGroup.affineScheme.{u} := prod.snd
  have hA0 := congrArg (fun q => q.left ≫ piK) hE
  have hB0 := congrArg (fun q => q.left ≫ piR) hU
  change iA.hom ≫ E.left ≫ piK = (specUnitMap EA u).left ≫ piK at hA0
  change iB.hom ≫ U.left ≫ piR = (specUnitMap SA v).left ≫ piR at hB0
  have hRect := scalar_product_inverse_swap k A R X e
  exact original_unit_rectangle EA SA Z iA iB
    (Algebra.TensorProduct.comm k A R).toRingHom u v
    (U.left ≫ piR) (E.left ≫ piK) hA0 hB0 hRect hUnit

private theorem tensorSpec_unit_map {k : Type u} [CommRing k]
    {A B C D : CommAlgCat.{u} k} (f : A ⟶ C) (g : B ⟶ D)
    (u : ((A ⊗ B : CommAlgCat.{u} k))ˣ) :
    ((algSpec (CommRingCat.of k)).map f.op ⊗ₘ (algSpec (CommRingCat.of k)).map g.op) ≫
        (algSpecTensorIso A B).hom ≫ specUnitMap (A ⊗ B) u =
      (algSpecTensorIso C D).hom ≫
        specUnitMap (C ⊗ D) (Units.map (f ⊗ₘ g).hom.toMonoidHom u) := by
  have h :
      ((algSpec (CommRingCat.of k)).map f.op ⊗ₘ (algSpec (CommRingCat.of k)).map g.op) ≫
          (algSpecTensorIso A B).hom =
        (algSpecTensorIso C D).hom ≫ (algSpec (CommRingCat.of k)).map (f ⊗ₘ g).op :=
    Functor.LaxMonoidal.μ_natural (AlgebraicGeometry.algSpec (CommRingCat.of k)) f.op g.op
  rw [← Category.assoc, h, Category.assoc, specUnitMap_naturality]

private theorem coevaluationUnit_bidual_coordinates {k : Type u} [Field k]
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    {B : CommHopfAlgCat.{u} k} [Coalgebra.IsCocomm k B] [FiniteDimensional k B]
    (c : CommHopfAlgCat.of k (Dual k A) ≅ B) :
    Units.map (Algebra.TensorProduct.map c.inv.hom.toAlgHom
        ((Module.Dual.evalAlgEquiv k A).symm.toAlgHom.comp c.hom.hom.dual.toAlgHom)).toMonoidHom
        (HopfAlgebra.coevaluationUnit k B) =
      Units.map (Algebra.TensorProduct.comm k A (Dual k A)).toAlgHom.toMonoidHom
        (HopfAlgebra.coevaluationUnit k A) := by
  let D := CommHopfAlgCat.of k (Dual k A)
  let q : Dual k B →ₐ[k] A :=
    (Module.Dual.evalAlgEquiv k A).symm.toAlgHom.comp c.hom.hom.dual.toAlgHom
  have hdual : c.hom.hom.dual.toAlgHom.comp c.inv.hom.dual.toAlgHom = AlgHom.id k (Dual k D) := by
    ext f a
    change f (c.inv.hom (c.hom.hom a)) = f a
    have h := congrArg (fun z : D ⟶ D => z.hom a) c.hom_inv_id
    exact congrArg f h
  have hq : q.toLinearMap ∘ₗ c.inv.hom.toLinearMap.dualMap =
      (Module.Dual.evalAlgEquiv k A).symm.toAlgHom.toLinearMap := by
    have h := congrArg (fun z : Dual k D →ₐ[k] Dual k D =>
      (Module.Dual.evalAlgEquiv k A).symm.toAlgHom.comp z) hdual
    have hl := congrArg AlgHom.toLinearMap h
    exact hl
  have hn := TensorProduct.coevaluation_naturality_apply c.inv.hom.toLinearMap 1
  have hm := congrArg (TensorProduct.map (LinearMap.id : D →ₗ[k] D) q.toLinearMap) hn
  simp only [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp] at hm
  rw [hq] at hm
  have hf0 := coevaluationUnit_flip A
  have hf := congrArg (fun z : (Dual k A ⊗[k] A)ˣ => (z : Dual k A ⊗[k] A)) hf0
  apply Units.ext
  have h := hm.trans hf
  exact h

private theorem native_bidual_pairing_coordinates {k : Type u} [Field k]
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    {B : CommHopfAlgCat.{u} k} [Coalgebra.IsCocomm k B] [FiniteDimensional k B]
    (c : CommHopfAlgCat.of k (Dual k A) ≅ B) :
    let q := (Module.Dual.evalAlgEquiv k A).symm.toAlgHom.comp c.hom.hom.dual.toAlgHom
    ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom c.inv.hom.toAlgHom).op ⊗ₘ
        (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom q).op) ≫
        (algSpecTensorIso (CommAlgCat.of k B) (CommAlgCat.of k (Dual k B))).hom ≫
        specUnitMap (CommAlgCat.of k B ⊗ CommAlgCat.of k (Dual k B))
          (HopfAlgebra.coevaluationUnit k B) =
      (algSpecTensorIso (CommAlgCat.of k (Dual k A)) (CommAlgCat.of k A)).hom ≫
        specUnitMap (CommAlgCat.of k (Dual k A) ⊗ CommAlgCat.of k A)
          (Units.map (Algebra.TensorProduct.comm k A (Dual k A)).toAlgHom.toMonoidHom
            (HopfAlgebra.coevaluationUnit k A)) := by
  dsimp only
  have h0 := tensorSpec_unit_map (CommAlgCat.ofHom c.inv.hom.toAlgHom)
    (CommAlgCat.ofHom
      ((Module.Dual.evalAlgEquiv k A).symm.toAlgHom.comp c.hom.hom.dual.toAlgHom))
    (HopfAlgebra.coevaluationUnit k B)
  have h1 := congrArg (fun v =>
    (algSpecTensorIso (CommAlgCat.of k (Dual k A)) (CommAlgCat.of k A)).hom ≫
      specUnitMap (CommAlgCat.of k (Dual k A) ⊗ CommAlgCat.of k A) v)
    (coevaluationUnit_bidual_coordinates A c)
  exact h0.trans h1

private theorem tensor_pair_factor {C : Type*} [Category C] [MonoidalCategory C]
    {X A D B DB : C} (e : X ≅ A) (a : D ⟶ B) (p : X ⟶ DB) (q : A ⟶ DB)
    (hp : p = e.hom ≫ q) :
    (𝟙 D ⊗ₘ p) ≫ (a ⊗ₘ 𝟙 DB) = (𝟙 D ⊗ₘ e.hom) ≫ (a ⊗ₘ q) := by
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id, hp]

private theorem bidual_pairing_diagram {C : Type*} [Category C]
    [CartesianMonoidalCategory C] [SymmetricCategory C] {X A D B DB M : C}
    (e : X ≅ A) (a : D ⟶ B) (p : X ⟶ DB) (q : A ⟶ DB)
    (EB : D ⊗ DB ⟶ M) (UB : B ⊗ DB ⟶ M) (V : D ⊗ A ⟶ M) (W : X ⊗ D ⟶ M)
    (hp : p = e.hom ≫ q) (hB : EB = (a ⊗ₘ 𝟙 DB) ≫ UB)
    (hpair : (a ⊗ₘ q) ≫ UB = V)
    (hV : V = (𝟙 D ⊗ₘ e.inv) ≫ (β_ D X).hom ≫ W) :
    (β_ X D).hom ≫ (𝟙 D ⊗ₘ p) ≫ EB = W := by
  rw [hB, ← Category.assoc (𝟙 D ⊗ₘ p) (a ⊗ₘ 𝟙 DB), tensor_pair_factor e a p q hp,
    Category.assoc, hpair, hV]
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    Iso.hom_inv_id, id_tensorHom_id, Category.comp_id, SymmetricCategory.symmetry,
    Category.id_comp]

private theorem map_triple_iso_hom {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z W : C} (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ W) :
    F.map (a ≪≫ b ≪≫ c).hom = F.map a.hom ≫ F.map b.hom ≫ F.map c.hom := by
  simp only [Iso.trans_hom, CategoryTheory.Functor.map_comp]

private theorem native_bidual_map_coordinates {k : Type u} [Field k]
    (A : CommHopfAlgCat.{u} k) [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    {B : CommHopfAlgCat.{u} k} [Coalgebra.IsCocomm k B] [FiniteDimensional k B]
    (c : CommHopfAlgCat.of k (Dual k A) ≅ B)
    {X : Grp (FScheme k)} (e : specGroup A ≅ X) :
    (e.symm ≪≫ specGroupBidualIso A ≪≫
        specGroupDualIso (A := CommHopfAlgCat.of k (Dual k A)) (B := B) c).hom.hom.hom =
      e.inv.hom.hom ≫ (algSpec (CommRingCat.of k)).map
        (CommAlgCat.ofHom
          ((Module.Dual.evalAlgEquiv k A).symm.toAlgHom.comp c.hom.hom.dual.toAlgHom)).op := by
  let F := algSpec (CommRingCat.of k)
  have h0 := map_triple_iso_hom (Grp.forget (FScheme k)) e.symm
    (specGroupBidualIso A)
    (specGroupDualIso (A := CommHopfAlgCat.of k (Dual k A)) (B := B) c)
  have h1 : (specGroupBidualIso A).hom.hom.hom =
      F.map (CommAlgCat.ofHom (Module.Dual.evalAlgEquiv k A).symm.toAlgHom :
        CommAlgCat.of k (Dual k (Dual k A)) ⟶ CommAlgCat.of k A).op := by
    rw [← hopfSpec_hopfBidualIso_inv]
    change F.map (CommAlgCat.ofHom (hopfBidualIso A).inv.hom.toAlgHom).op = _
    rw [hopfBidualIso_inv_hom]
    rfl
  have h2 := congrArg (fun m => e.inv.hom.hom ≫ m ≫
    (specGroupDualIso (A := CommHopfAlgCat.of k (Dual k A)) (B := B) c).hom.hom.hom) h1
  have h3 := congrArg (fun m => e.inv.hom.hom ≫
    F.map (CommAlgCat.ofHom (Module.Dual.evalAlgEquiv k A).symm.toAlgHom :
      CommAlgCat.of k (Dual k (Dual k A)) ⟶ CommAlgCat.of k A).op ≫ m)
    (congrArg ((Grp.forget (FScheme k)).map)
      (hopfSpec_specGroupDualIso_hom c).symm)
  have h := h0.trans (h2.trans h3)
  have hf : F.map (CommAlgCat.ofHom (Module.Dual.evalAlgEquiv k A).symm.toAlgHom :
      CommAlgCat.of k (Dual k (Dual k A)) ⟶ CommAlgCat.of k A).op ≫
      F.map (CommAlgCat.ofHom c.hom.hom.dual.toAlgHom).op =
    F.map (CommAlgCat.ofHom
      ((Module.Dual.evalAlgEquiv k A).symm.toAlgHom.comp c.hom.hom.dual.toAlgHom)).op := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp]
    rfl
  exact h.trans (congrArg (fun m => e.inv.hom.hom ≫ m) hf)

section SecondVariableCoordinates

variable {k : Type u} [Field k]

private def secondCharacterAffine (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    (Over.pullback (Spec.algebraMap k A)).mapGrp.obj
        (specGroup (CommHopfAlgCat.of k (Dual k A))) ⟶
      MultiplicativeGroup.groupScheme (Spec (CommRingCat.of A)) :=
  (hopfSpecScalarExtensionIso k A (CommHopfAlgCat.of k (Dual k A))).hom ≫
    scalarCharacterEquiv (CommHopfAlgCat.of k (Dual k A)) A
      (Module.Dual.evalAlgEquiv k A).symm.toAlgHom

private theorem secondCharacterAffine_coordinates (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    (hopfSpecScalarExtensionIso k A (CommHopfAlgCat.of k (Dual k A))).inv ≫
        secondCharacterAffine A =
      scalarCharacterEquiv (CommHopfAlgCat.of k (Dual k A)) A
        (Module.Dual.evalAlgEquiv k A).symm.toAlgHom := by
  have h := Iso.inv_hom_id_assoc
    (hopfSpecScalarExtensionIso k A (CommHopfAlgCat.of k (Dual k A)))
    (scalarCharacterEquiv (CommHopfAlgCat.of k (Dual k A)) A
      (Module.Dual.evalAlgEquiv k A).symm.toAlgHom)
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h
  dsimp only [secondCharacterAffine]
  exact h

private theorem secondCharacterAffine_specUnitMap (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    (hopfSpecScalarExtensionIso k A (CommHopfAlgCat.of k (Dual k A))).inv.hom.hom ≫
        (secondCharacterAffine A).hom.hom =
      specUnitMap (CommAlgCat.of A (A ⊗[k] Dual k A)) (HopfAlgebra.coevaluationUnit k A) := by
  have h0 := secondCharacterAffine_coordinates A
  have h1 := congrArg ((Grp.forget (Over (Spec (CommRingCat.of A)))).map) h0
  have h2 := scalarCharacter_specUnitMap_second
    (CommHopfAlgCat.of k (Dual k A)) A (Module.Dual.evalAlgEquiv k A).symm.toAlgHom
  have hu := secondCharacterUnit_eq A
  have h3 := congrArg (specUnitMap (CommAlgCat.of A (A ⊗[k] Dual k A))) hu
  have h := h1.trans (h2.trans h3)
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def secondEvaluationAffine (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    (specGroup (CommHopfAlgCat.of k (Dual k A))).X ⊗
        (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)) ⟶
      MultiplicativeGroup.scheme (Base k) :=
  let D := CommHopfAlgCat.of k (Dual k A)
  let R : CommAlgCat.{u} k := CommAlgCat.of k A
  let P := MonoidalCategory.tensorIso
      ((Grp.forget (FScheme k)).mapIso (Iso.refl (specGroup D)))
      (Iso.refl ((algSpec (CommRingCat.of k)).obj (op R))) ≪≫
    algSpecTensorIso (CommAlgCat.of k D) R
  let u : ((CommAlgCat.of k D ⊗ R : CommAlgCat.{u} k))ˣ :=
    Units.map (Algebra.TensorProduct.comm k A (Dual k A)).toAlgHom.toMonoidHom
      (HopfAlgebra.coevaluationUnit k A)
  P.hom ≫ specUnitMap (CommAlgCat.of k D ⊗ R) u

private theorem secondCharacterAffine_evaluation (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    (secondCharacterAffine A).hom.hom.left ≫ prod.snd =
      (secondEvaluationAffine A).left ≫ prod.snd := by
  let D := CommHopfAlgCat.of k (Dual k A)
  let R : CommAlgCat.{u} k := CommAlgCat.of k A
  let P := MonoidalCategory.tensorIso
      ((Grp.forget (FScheme k)).mapIso (Iso.refl (specGroup D)))
      (Iso.refl ((algSpec (CommRingCat.of k)).obj (op R))) ≪≫
    algSpecTensorIso (CommAlgCat.of k D) R
  let u : ((CommAlgCat.of k D ⊗ R : CommAlgCat.{u} k))ˣ :=
    Units.map (Algebra.TensorProduct.comm k A (Dual k A)).toAlgHom.toMonoidHom
      (HopfAlgebra.coevaluationUnit k A)
  let v : (CommAlgCat.of R (R ⊗[k] D))ˣ := HopfAlgebra.coevaluationUnit k A
  let U : ((Over.pullback (Spec.algebraMap k R)).mapGrp.obj (specGroup D)).X ⟶
      MultiplicativeGroup.scheme (Spec (CommRingCat.of R)) :=
    (secondCharacterAffine A).hom.hom
  have h0 := native_evaluation_comparison k D R (specGroup D) (Iso.refl _)
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h0
  have hE := Iso.inv_hom_id_assoc P (specUnitMap (CommAlgCat.of k D ⊗ R) u)
  have hr0 := mapIso_refl_trans_inv_comp
    (Over.pullback (Spec.algebraMap k A)).mapGrp
    (specGroup D) (hopfSpecScalarExtensionIso k A D) (secondCharacterAffine A)
  have hr := congrArg ((Grp.forget (Over (Spec (CommRingCat.of A)))).map) hr0
  have hU0 := hr.trans (secondCharacterAffine_specUnitMap A)
  have hUnit : Units.map (Algebra.TensorProduct.comm k D R).toRingHom.toMonoidHom u = v := by
    apply Units.ext
    change Algebra.TensorProduct.comm k (Dual k A) A
      (Algebra.TensorProduct.comm k A (Dual k A) (coevaluation k A 1)) = coevaluation k A 1
    exact (Algebra.TensorProduct.comm k A (Dual k A)).symm_apply_apply _
  have hp := h0 u v (secondEvaluationAffine A) U
  have hp1 := hp hE
  have hp2 := hp1 hU0
  exact hp2 hUnit

private def dualSpecCoordinates_second (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    (specGroup (CommHopfAlgCat.of k (Dual k A))).X ≅
      (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k (Dual k A))) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def coordinateEvaluation_second (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    {X : Grp (FScheme k)} (e : specGroup A ≅ X) :
    X.X ⊗ (specGroup (CommHopfAlgCat.of k (Dual k A))).X ⟶
      MultiplicativeGroup.scheme (Base k) :=
  ((MonoidalCategory.tensorIso ((Grp.forget (FScheme k)).mapIso e.symm)
      (Iso.refl (specGroup (CommHopfAlgCat.of k (Dual k A))).X)) ≪≫
    algSpecTensorIso (CommAlgCat.of k A) (CommAlgCat.of k (Dual k A))).hom ≫
      specUnitMap (CommAlgCat.of k A ⊗ CommAlgCat.of k (Dual k A))
        (HopfAlgebra.coevaluationUnit k A)

private theorem secondEvaluationAffine_transport (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    {X : Grp (FScheme k)} (e : specGroup A ≅ X) :
    secondEvaluationAffine A =
      (𝟙 (specGroup (CommHopfAlgCat.of k (Dual k A))).X ⊗ₘ e.hom.hom.hom) ≫
        (β_ (specGroup (CommHopfAlgCat.of k (Dual k A))).X X.X).hom ≫
        coordinateEvaluation_second A e := by
  have h0 := unit_product_transpose k (CommAlgCat.of k A)
    (CommAlgCat.of k (Dual k A))
    ((Grp.forget (FScheme k)).mapIso e.symm) (dualSpecCoordinates_second A)
    (HopfAlgebra.coevaluationUnit k A)
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h0
  dsimp only [secondEvaluationAffine, coordinateEvaluation_second, dualSpecCoordinates_second]
  exact h0



private theorem tensor_comparison_formula {C : Type*} [Category C]
    [MonoidalCategory C] {X A D Q M : C} (e : X ≅ A) (t : A ⊗ D ≅ Q) (u : Q ⟶ M) :
    ((MonoidalCategory.tensorIso e (Iso.refl D)) ≪≫ t).hom ≫ u =
      (e.hom ⊗ₘ 𝟙 D) ≫ t.hom ≫ u := by
  simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom, Iso.refl_hom, Category.assoc]

private theorem tensor_comparison_refl {C D : Type*} [Category C] [Category D]
    [MonoidalCategory D] (F : C ⥤ D) (X : C) (Y : D) {Q M : D}
    (t : F.obj X ⊗ Y ≅ Q) (u : Q ⟶ M) :
    ((MonoidalCategory.tensorIso (F.mapIso (Iso.refl X)) (Iso.refl Y)) ≪≫ t).hom ≫ u =
      t.hom ≫ u := by
  have h : MonoidalCategory.tensorIso (Iso.refl (F.obj X)) (Iso.refl Y) =
      Iso.refl (F.obj X ⊗ Y) := by
    apply Iso.ext
    exact id_tensorHom_id _ _
  rw [CategoryTheory.Functor.mapIso_refl, h, Iso.refl_trans]

private theorem secondEvaluationAffine_plain (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A] :
    secondEvaluationAffine A =
      (algSpecTensorIso (CommAlgCat.of k (Dual k A)) (CommAlgCat.of k A)).hom ≫
        specUnitMap (CommAlgCat.of k (Dual k A) ⊗ CommAlgCat.of k A)
          (Units.map (Algebra.TensorProduct.comm k A (Dual k A)).toAlgHom.toMonoidHom
            (HopfAlgebra.coevaluationUnit k A)) := by
  have h := tensor_comparison_refl (Grp.forget (FScheme k))
    (specGroup (CommHopfAlgCat.of k (Dual k A)))
    ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k A)))
    (algSpecTensorIso (CommAlgCat.of k (Dual k A)) (CommAlgCat.of k A))
    (specUnitMap (CommAlgCat.of k (Dual k A) ⊗ CommAlgCat.of k A)
      (Units.map (Algebra.TensorProduct.comm k A (Dual k A)).toAlgHom.toMonoidHom
        (HopfAlgebra.coevaluationUnit k A)))
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h
  dsimp only [secondEvaluationAffine]
  exact h

private theorem coordinateEvaluation_second_formula (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    {X : Grp (FScheme k)} (e : specGroup A ≅ X) :
    coordinateEvaluation_second A e =
      (e.inv.hom.hom ⊗ₘ 𝟙 (specGroup (CommHopfAlgCat.of k (Dual k A))).X) ≫
        (algSpecTensorIso (CommAlgCat.of k A) (CommAlgCat.of k (Dual k A))).hom ≫
        specUnitMap (CommAlgCat.of k A ⊗ CommAlgCat.of k (Dual k A))
          (HopfAlgebra.coevaluationUnit k A) := by
  have h := tensor_comparison_formula ((Grp.forget (FScheme k)).mapIso e.symm)
    (algSpecTensorIso (CommAlgCat.of k A) (CommAlgCat.of k (Dual k A)))
    (specUnitMap (CommAlgCat.of k A ⊗ CommAlgCat.of k (Dual k A))
      (HopfAlgebra.coevaluationUnit k A))
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h
  dsimp only [coordinateEvaluation_second]
  exact h

private theorem spec_comparison_inverse {C D : Type*} [Category C] [Category D]
    (F : Cᵒᵖ ⥤ D) {A B : C} (e : A ≅ B)
    (t : F.obj (op B) ≅ F.obj (op A)) (ht : F.map e.hom.op = t.hom) :
    F.map e.inv.op = t.inv := by
  apply (cancel_mono t.hom).1
  rw [← ht, ← CategoryTheory.Functor.map_comp, ← op_comp,
    Iso.hom_inv_id, op_id, CategoryTheory.Functor.map_id, ht, Iso.inv_hom_id]

private theorem coordinateEvaluation_second_bidual (A : CommHopfAlgCat.{u} k)
    [Coalgebra.IsCocomm k A] [FiniteDimensional k A]
    {B : CommHopfAlgCat.{u} k} [Coalgebra.IsCocomm k B] [FiniteDimensional k B]
    {X : Grp (FScheme k)} (e : specGroup A ≅ X)
    (c : CommHopfAlgCat.of k (Dual k A) ≅ B)
    (eD : specGroup B ≅ specGroup (CommHopfAlgCat.of k (Dual k A)))
    (hMap : (hopfSpec (CommRingCat.of k)).map c.hom.op = eD.hom) :
    (β_ X.X (specGroup (CommHopfAlgCat.of k (Dual k A))).X).hom ≫
        (𝟙 (specGroup (CommHopfAlgCat.of k (Dual k A))).X ⊗ₘ
          (e.symm ≪≫ specGroupBidualIso A ≪≫
            specGroupDualIso (A := CommHopfAlgCat.of k (Dual k A)) (B := B) c).hom.hom.hom) ≫
        coordinateEvaluation_second B eD = coordinateEvaluation_second A e := by
  let D := CommHopfAlgCat.of k (Dual k A)
  let F := algSpec (CommRingCat.of k)
  let q := (Module.Dual.evalAlgEquiv k A).symm.toAlgHom.comp c.hom.hom.dual.toAlgHom
  let a := F.map (CommAlgCat.ofHom c.inv.hom.toAlgHom).op
  let b := F.map (CommAlgCat.ofHom q).op
  let UB := (algSpecTensorIso (CommAlgCat.of k B) (CommAlgCat.of k (Dual k B))).hom ≫
    specUnitMap (CommAlgCat.of k B ⊗ CommAlgCat.of k (Dual k B)) (HopfAlgebra.coevaluationUnit k B)
  have hInv0 := spec_comparison_inverse (hopfSpec (CommRingCat.of k)) c
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at hInv0
  have hInv := congrArg ((Grp.forget (FScheme k)).map) (hInv0 eD hMap)
  change a = eD.inv.hom.hom at hInv
  have hB0 := coordinateEvaluation_second_formula B eD
  have hB1 := congrArg (fun z => (z ⊗ₘ 𝟙 (specGroup (CommHopfAlgCat.of k (Dual k B))).X) ≫ UB)
    hInv.symm
  have hB := hB0.trans hB1
  have hP0 := native_bidual_pairing_coordinates A c
  have hP := hP0.trans (secondEvaluationAffine_plain A).symm
  have hV := secondEvaluationAffine_transport A e
  have hp := native_bidual_map_coordinates A c e
  have h0 := bidual_pairing_diagram ((Grp.forget (FScheme k)).mapIso e.symm) a
    (e.symm ≪≫ specGroupBidualIso A ≪≫
      specGroupDualIso (A := D) (B := B) c).hom.hom.hom b
    (coordinateEvaluation_second B eD) UB (secondEvaluationAffine A)
    (coordinateEvaluation_second A e)
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h0 hB hP hV hp
  exact h0 hp hB hP hV

end SecondVariableCoordinates

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]

/-- The inverse product comparison retains the original first projection. -/
theorem coordinateProductIso_inv_fst :
    (coordinateProductIso (k := k) G).inv ≫ fst G.X (dualGroup (k := k) G).X =
      (algSpecTensorIso (CommAlgCat.of k (coordinateHopf (k := k) G))
          (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G)))).inv ≫
        fst (specGroup (k := k) (coordinateHopf (k := k) G)).X (dualGroup (k := k) G).X ≫
          (coordinateSpecIso (k := k) G).hom.hom.hom := by
  have h := comparison_inv_fst
    (algSpecTensorIso (CommAlgCat.of k (coordinateHopf (k := k) G))
      (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G))))
    ((Grp.forget (FScheme k)).mapIso (coordinateSpecIso (k := k) G).symm)
  dsimp only [coordinateProductIso]
  exact h

/-- The inverse product comparison retains the original dual projection. -/
theorem coordinateProductIso_inv_snd :
    (coordinateProductIso (k := k) G).inv ≫ snd G.X (dualGroup (k := k) G).X =
      (algSpecTensorIso (CommAlgCat.of k (coordinateHopf (k := k) G))
          (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G)))).inv ≫
        snd (specGroup (k := k) (coordinateHopf (k := k) G)).X (dualGroup (k := k) G).X := by
  have h := comparison_inv_snd
    (algSpecTensorIso (CommAlgCat.of k (coordinateHopf (k := k) G))
      (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G))))
    ((Grp.forget (FScheme k)).mapIso (coordinateSpecIso (k := k) G).symm)
  dsimp only [coordinateProductIso]
  exact h

/-- The original first projection is the native algebraic tensor-inclusion arrow. -/
theorem coordinateProductIso_inv_fst_coordinates :
    (coordinateProductIso (k := k) G).inv ≫ fst G.X (dualGroup (k := k) G).X =
      (algSpec (CommRingCat.of k)).map
          (fst (op (CommAlgCat.of k (coordinateHopf (k := k) G)))
            (op (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G))))) ≫
        (coordinateSpecIso (k := k) G).hom.hom.hom := by
  have h := specComparison_inv_fst k
    (CommAlgCat.of k (coordinateHopf (k := k) G))
    (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G)))
    ((Grp.forget (FScheme k)).mapIso (coordinateSpecIso (k := k) G).symm)
  dsimp only [coordinateProductIso]
  exact h

/-- The original dual projection is the native algebraic tensor-inclusion arrow. -/
theorem coordinateProductIso_inv_snd_coordinates :
    (coordinateProductIso (k := k) G).inv ≫ snd G.X (dualGroup (k := k) G).X =
      (algSpec (CommRingCat.of k)).map
        (snd (op (CommAlgCat.of k (coordinateHopf (k := k) G)))
          (op (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G))))) := by
  have h := specComparison_inv_snd k
    (CommAlgCat.of k (coordinateHopf (k := k) G))
    (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G)))
    ((Grp.forget (FScheme k)).mapIso (coordinateSpecIso (k := k) G).symm)
  dsimp only [coordinateProductIso]
  exact h

/-- The inverse product comparison retains the first native scheme projection. -/
theorem coordinateProductIso_inv_fst_left :
    (coordinateProductIso (k := k) G).inv.left ≫ (fst G.X (dualGroup (k := k) G).X).left =
      ((algSpec (CommRingCat.of k)).map
          (fst (op (CommAlgCat.of k (coordinateHopf (k := k) G)))
            (op (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G)))))).left ≫
        (coordinateSpecIso (k := k) G).hom.hom.hom.left := by
  exact congrArg Over.Hom.left (coordinateProductIso_inv_fst_coordinates (k := k) G)

/-- The inverse product comparison retains the dual native scheme projection. -/
theorem coordinateProductIso_inv_snd_left :
    (coordinateProductIso (k := k) G).inv.left ≫ (snd G.X (dualGroup (k := k) G).X).left =
      ((algSpec (CommRingCat.of k)).map
        (snd (op (CommAlgCat.of k (coordinateHopf (k := k) G)))
          (op (CommAlgCat.of k (Dual k (coordinateHopf (k := k) G)))))).left := by
  exact congrArg Over.Hom.left (coordinateProductIso_inv_snd_coordinates (k := k) G)

/-- The original universal character and frozen evaluation have the same Laurent coordinate. -/
theorem universalCharacter_evaluation :
    (universalCharacter (k := k) G).hom.hom.left ≫ prod.snd =
      (evaluation (k := k) G).left ≫ prod.snd := by
  let A := coordinateHopf (k := k) G
  let R : CommAlgCat.{u} k := CommAlgCat.of k (Dual k A)
  have h0 := native_evaluation_comparison k A R G (coordinateSpecIso (k := k) G)
  let U0 : ((Over.pullback (Spec.algebraMap k R)).mapGrp.obj G).X ⟶
      MultiplicativeGroup.scheme (Spec (CommRingCat.of R)) :=
    (universalCharacter (k := k) G).hom.hom
  have hE := evaluation_coordinate (k := k) G
  have hU := universalCharacter_specUnitMap (k := k) G
  have hu0 := evaluationUnit_eq (k := k) G
  have hu := congrArg
    (fun u : (evaluationAlgebra (k := k) G)ˣ =>
      Units.map (Algebra.TensorProduct.comm k A R).toRingHom.toMonoidHom u) hu0
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h0 hE hU hu
  have hf := h0 (evaluationUnit (k := k) G)
    (Units.map (Algebra.TensorProduct.comm k A R).toRingHom.toMonoidHom
      (HopfAlgebra.coevaluationUnit k A))
    (evaluation (k := k) G) U0
  dsimp only [coordinateProductIso, coordinateScalarExtensionIso, evaluationAlgebra] at hE hU
  have hf1 := hf hE
  have hf2 := hf1 hU
  exact hf2 hu

/-- The native group character is the canonical lift of the frozen evaluation over the dual. -/
theorem universalCharacter_evaluation_map :
    (universalCharacter (k := k) G).hom.hom.left =
      prod.lift
        ((Over.pullback (dualGroup (k := k) G).X.hom).mapGrp.obj G).X.hom
        ((evaluation (k := k) G).left ≫ prod.snd) := by
  apply prod.hom_ext
  · rw [prod.lift_fst]
    exact (universalCharacter (k := k) G).hom.hom.w
  · rw [prod.lift_snd]
    exact universalCharacter_evaluation (k := k) G

/-- The original evaluation viewed over its same dual base. -/
def evaluationOverDual :
    ((Over.pullback (dualGroup (k := k) G).X.hom).mapGrp.obj G).X ⟶
      MultiplicativeGroup.scheme (dualGroup (k := k) G).X.left :=
  Over.homMk
    (prod.lift
      ((Over.pullback (dualGroup (k := k) G).X.hom).mapGrp.obj G).X.hom
      ((evaluation (k := k) G).left ≫ prod.snd))
    (by simp [MultiplicativeGroup.scheme])

/-- This is the same existing universal group character on underlying Over morphisms. -/
theorem evaluationOverDual_eq_universal :
    evaluationOverDual (k := k) G = (universalCharacter (k := k) G).hom.hom := by
  apply Over.OverMorphism.ext
  exact (universalCharacter_evaluation_map (k := k) G).symm

local instance instGrpObjGmOverDual :
    GrpObj (MultiplicativeGroup.scheme (dualGroup (k := k) G).X.left) :=
  (MultiplicativeGroup.groupScheme (dualGroup (k := k) G).X.left).grp

/-- The original evaluation is a group character in the original first variable. -/
theorem evaluationOverDual_isMonHom : IsMonHom (evaluationOverDual (k := k) G) := by
  rw [evaluationOverDual_eq_universal]
  exact (universalCharacter (k := k) G).hom.isMonHom_hom

/-- The original evaluation takes the first identity section to the identity. -/
theorem evaluationOverDual_one :
    η[((Over.pullback (dualGroup (k := k) G).X.hom).mapGrp.obj G).X] ≫
        evaluationOverDual (k := k) G =
      η[MultiplicativeGroup.scheme (dualGroup (k := k) G).X.left] := by
  let : IsMonHom (evaluationOverDual (k := k) G) := evaluationOverDual_isMonHom (k := k) G
  exact IsMonHom.one_hom _

/-- Multiplicativity of the original evaluation in the original first variable. -/
theorem evaluationOverDual_mul :
    μ[((Over.pullback (dualGroup (k := k) G).X.hom).mapGrp.obj G).X] ≫
        evaluationOverDual (k := k) G =
      (evaluationOverDual (k := k) G ⊗ₘ evaluationOverDual (k := k) G) ≫
        μ[MultiplicativeGroup.scheme (dualGroup (k := k) G).X.left] := by
  let : IsMonHom (evaluationOverDual (k := k) G) := evaluationOverDual_isMonHom (k := k) G
  exact IsMonHom.mul_hom _

variable {G} {H : Grp (FScheme k)} [IsFinite H.X.hom] [IsCommMonObj H.X]

/-- The original pairing is natural for the original group map and its selected dual. -/
theorem evaluation_naturality (f : G ⟶ H) :
    (f.hom.hom ⊗ₘ 𝟙 (dualGroup H).X) ≫ evaluation H =
      (𝟙 G.X ⊗ₘ (dualMap f).hom.hom) ≫ evaluation G := by
  have hn := native_pairing_naturality (coordinateMap f)
  have hc0 := hopfSpec_coordinateMap f
  have hc := congrArg
    (fun q : specGroup (coordinateHopf G) ⟶ specGroup (coordinateHopf H) => q.hom.hom) hc0
  have ht := pairing_transport_naturality
    ((Grp.forget (FScheme k)).mapIso (coordinateSpecIso G).symm)
    ((Grp.forget (FScheme k)).mapIso (coordinateSpecIso H).symm)
    f.hom.hom
    ((AlgebraicGeometry.algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (coordinateMap f).hom.toAlgHom).op)
    ((dualMap f).hom.hom)
    ((algSpecTensorIso (CommAlgCat.of k (coordinateHopf G))
      (CommAlgCat.of k (Dual k (coordinateHopf G)))).hom ≫
      specUnitMap (evaluationAlgebra G) (evaluationUnit G))
    ((algSpecTensorIso (CommAlgCat.of k (coordinateHopf H))
      (CommAlgCat.of k (Dual k (coordinateHopf H)))).hom ≫
      specUnitMap (evaluationAlgebra H) (evaluationUnit H))
  have ht1 := ht hc.symm
  have ht2 := ht1 hn
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at ht2
  dsimp only [evaluation, coordinateProductIso]
  exact ht2


variable (G)

/-- Every original test-point character is the same original evaluation pulled back to that test. -/
theorem characterOfPoint_evaluation (T : FScheme k) (p : T ⟶ (dualGroup G).X) :
    (characterOfPoint G T p).hom.hom.left ≫ prod.snd =
      groupPullbackBaseMap G p ≫ (evaluation G).left ≫ prod.snd := by
  exact (characterOfPoint_coordinates G T p).trans
    (congrArg (fun q => groupPullbackBaseMap G p ≫ q) (universalCharacter_evaluation G))

/-- The full original character over any test is the canonical lift of the original evaluation. -/
theorem characterOfPoint_evaluation_map (T : FScheme k) (p : T ⟶ (dualGroup G).X) :
    (characterOfPoint G T p).hom.hom.left =
      prod.lift ((Over.pullback T.hom).mapGrp.obj G).X.hom
        (groupPullbackBaseMap G p ≫ (evaluation G).left ≫ prod.snd) := by
  apply prod.hom_ext
  · rw [prod.lift_fst]
    exact (characterOfPoint G T p).hom.hom.w
  · rw [prod.lift_snd]
    exact characterOfPoint_evaluation G T p

/-- The same native dual pullback represents characters after any original base change. -/
def characterEquivBaseChange (T : FScheme k) (U : Over T.left) :
    (U ⟶ ((Over.pullback T.hom).mapGrp.obj (dualGroup G)).X) ≃
      ((Over.pullback U.hom).mapGrp.obj ((Over.pullback T.hom).mapGrp.obj G) ⟶
        MultiplicativeGroup.groupScheme U.left) :=
  ((Over.mapPullbackAdj T.hom).homEquiv U (dualGroup G).X).symm.trans
    ((characterEquiv G ((Over.map T.hom).obj U)).trans
      (Iso.homCongr ((BaseChange.groupSchemeBaseChangeComp U.hom T.hom).app G)
        (Iso.refl _)))

/-- Base-change representation uses the original pullback coherence and original character. -/
theorem characterEquivBaseChange_apply (T : FScheme k) (U : Over T.left)
    (p : U ⟶ ((Over.pullback T.hom).mapGrp.obj (dualGroup G)).X) :
    characterEquivBaseChange G T U p =
      ((BaseChange.groupSchemeBaseChangeComp U.hom T.hom).inv.app G) ≫
        characterEquiv G ((Over.map T.hom).obj U)
          (((Over.mapPullbackAdj T.hom).homEquiv U (dualGroup G).X).symm p) := by
  change ((BaseChange.groupSchemeBaseChangeComp U.hom T.hom).inv.app G) ≫
      characterEquiv G ((Over.map T.hom).obj U)
        (((Over.mapPullbackAdj T.hom).homEquiv U (dualGroup G).X).symm p) ≫
      𝟙 (MultiplicativeGroup.groupScheme U.left) = _
  exact congrArg (fun f => ((BaseChange.groupSchemeBaseChangeComp U.hom T.hom).inv.app G) ≫ f)
    (Category.comp_id (characterEquiv G ((Over.map T.hom).obj U)
      (((Over.mapPullbackAdj T.hom).homEquiv U (dualGroup G).X).symm p)))

/-- Canonical pullback comparison recovers the same original all-test character. -/
theorem characterEquivBaseChange_toOriginal (T : FScheme k) (U : Over T.left)
    (p : U ⟶ ((Over.pullback T.hom).mapGrp.obj (dualGroup G)).X) :
    ((BaseChange.groupSchemeBaseChangeComp U.hom T.hom).hom.app G) ≫
        characterEquivBaseChange G T U p =
      characterEquiv G ((Over.map T.hom).obj U)
        (((Over.mapPullbackAdj T.hom).homEquiv U (dualGroup G).X).symm p) := by
  let e := (BaseChange.groupSchemeBaseChangeComp U.hom T.hom).app G
  have h0 := congrArg (fun c => e.hom ≫ c) (characterEquivBaseChange_apply G T U p)
  have h1 := Iso.hom_inv_id_assoc e
    (characterEquiv G ((Over.map T.hom).obj U)
      (((Over.mapPullbackAdj T.hom).homEquiv U (dualGroup G).X).symm p))
  exact h0.trans h1

/-- The same native base-change bijection is natural after the canonical pullback comparisons. -/
theorem characterEquivBaseChange_naturality (T : FScheme k)
    {U V : Over T.left} (h : V ⟶ U)
    (p : U ⟶ ((Over.pullback T.hom).mapGrp.obj (dualGroup G)).X) :
    ((BaseChange.groupSchemeBaseChangeComp V.hom T.hom).hom.app G) ≫
        characterEquivBaseChange G T V (h ≫ p) =
      restrictCharacter G ((Over.map T.hom).map h)
        (((BaseChange.groupSchemeBaseChangeComp U.hom T.hom).hom.app G) ≫
          characterEquivBaseChange G T U p) := by
  have hq := (Over.mapPullbackAdj T.hom).homEquiv_naturality_left_symm h p
  have hq' := congrArg (characterEquiv G ((Over.map T.hom).obj V)) hq
  have hn := characterEquiv_naturality G ((Over.map T.hom).map h)
    (((Over.mapPullbackAdj T.hom).homEquiv U (dualGroup G).X).symm p)
  have hU := congrArg (restrictCharacter G ((Over.map T.hom).map h))
    (characterEquivBaseChange_toOriginal G T U p)
  exact (characterEquivBaseChange_toOriginal G T V (h ≫ p)).trans
    (hq'.trans (hn.trans hU.symm))


private theorem secondEvaluationAffine_original :
    secondEvaluationAffine (coordinateHopf G) =
      (𝟙 (dualGroup G).X ⊗ₘ (coordinateSpecIso G).hom.hom.hom) ≫
        (β_ (dualGroup G).X G.X).hom ≫ evaluation G := by
  have h0 := secondEvaluationAffine_transport (coordinateHopf G) (coordinateSpecIso G)
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h0
  dsimp only [coordinateEvaluation_second, evaluation, coordinateProductIso] at h0 ⊢
  exact h0

private def secondCharacterOriginal :
    (Over.pullback G.X.hom).mapGrp.obj (dualGroup G) ⟶
      MultiplicativeGroup.groupScheme G.X.left :=
  restrictCharacter (dualGroup G) (coordinateSpecIso G).inv.hom.hom
    (secondCharacterAffine (coordinateHopf G))

private theorem secondCharacterOriginal_coordinates :
    (secondCharacterOriginal G).hom.hom.left ≫ prod.snd =
      (β_ (dualGroup G).X G.X).hom.left ≫ (evaluation G).left ≫ prod.snd := by
  let q := (coordinateSpecIso G).inv.hom.hom
  have h1 := restrictCharacter_coordinates (dualGroup G) q
    (secondCharacterAffine (coordinateHopf G))
  have h2 := congrArg (fun m => groupPullbackBaseMap (dualGroup G) q ≫ m)
    (secondCharacterAffine_evaluation (coordinateHopf G))
  have h3 := congrArg (fun m => groupPullbackBaseMap (dualGroup G) q ≫
    (Over.forget (Base k)).map m ≫ prod.snd) (secondEvaluationAffine_original G)
  have hc := functor_tensor_inverse_cancel (Over.forget (Base k)) (dualGroup G).X
    ((Grp.forget (FScheme k)).mapIso (coordinateSpecIso G).symm)
    ((β_ (dualGroup G).X G.X).hom ≫ evaluation G)
  have h4 := congrArg (fun m => m ≫ prod.snd) hc
  have hp := congrArg (fun m => m ≫
    (Over.forget (Base k)).map
      ((𝟙 (dualGroup G).X ⊗ₘ (coordinateSpecIso G).hom.hom.hom) ≫
        (β_ (dualGroup G).X G.X).hom ≫ evaluation G) ≫ prod.snd)
    (groupPullbackBaseMap_tensor (dualGroup G) q)
  have h := h1.trans (h2.trans (h3.trans (hp.trans h4)))
  dsimp only [secondCharacterOriginal]
  exact h

/-- The original evaluation viewed over the same original primal group scheme. -/
def evaluationOverPrimal :
    ((Over.pullback G.X.hom).mapGrp.obj (dualGroup G)).X ⟶
      MultiplicativeGroup.scheme G.X.left :=
  Over.homMk (prod.lift ((Over.pullback G.X.hom).mapGrp.obj (dualGroup G)).X.hom
    ((β_ (dualGroup G).X G.X).hom.left ≫ (evaluation G).left ≫ prod.snd))
    (by simp [MultiplicativeGroup.scheme])

private theorem secondCharacterOriginal_evaluation_map :
    (secondCharacterOriginal G).hom.hom.left =
      prod.lift ((Over.pullback G.X.hom).mapGrp.obj (dualGroup G)).X.hom
        ((β_ (dualGroup G).X G.X).hom.left ≫ (evaluation G).left ≫ prod.snd) := by
  apply prod.hom_ext
  · rw [prod.lift_fst]
    exact (secondCharacterOriginal G).hom.hom.w
  · rw [prod.lift_snd]
    exact secondCharacterOriginal_coordinates G

private theorem evaluationOverPrimal_eq_character :
    evaluationOverPrimal G = (secondCharacterOriginal G).hom.hom := by
  apply Over.OverMorphism.ext
  exact (secondCharacterOriginal_evaluation_map G).symm

local instance instGrpObjGmOverPrimal : GrpObj (MultiplicativeGroup.scheme G.X.left) :=
  (MultiplicativeGroup.groupScheme G.X.left).grp

/-- The same original evaluation is a group character in its second variable. -/
theorem evaluationOverPrimal_isMonHom : IsMonHom (evaluationOverPrimal G) := by
  rw [evaluationOverPrimal_eq_character]
  exact (secondCharacterOriginal G).hom.isMonHom_hom

/-- The original evaluation takes the second identity section to the identity. -/
theorem evaluationOverPrimal_one :
    η[((Over.pullback G.X.hom).mapGrp.obj (dualGroup G)).X] ≫ evaluationOverPrimal G =
      η[MultiplicativeGroup.scheme G.X.left] := by
  let : IsMonHom (evaluationOverPrimal G) := evaluationOverPrimal_isMonHom G
  exact IsMonHom.one_hom _

/-- Multiplicativity of the same original evaluation in its second variable. -/
theorem evaluationOverPrimal_mul :
    μ[((Over.pullback G.X.hom).mapGrp.obj (dualGroup G)).X] ≫ evaluationOverPrimal G =
      (evaluationOverPrimal G ⊗ₘ evaluationOverPrimal G) ≫
        μ[MultiplicativeGroup.scheme G.X.left] := by
  let : IsMonHom (evaluationOverPrimal G) := evaluationOverPrimal_isMonHom G
  exact IsMonHom.mul_hom _


/-- The original bidual isomorphism transposes the same original evaluation pairing. -/
theorem evaluation_bidual :
    (β_ G.X (dualGroup G).X).hom ≫
        (𝟙 (dualGroup G).X ⊗ₘ (bidualIso G).hom.hom.hom) ≫
        evaluation (dualGroup G) = evaluation G := by
  have h0 := coordinateEvaluation_second_bidual (coordinateHopf G) (coordinateSpecIso G)
    (dualCoordinateIso G) (coordinateSpecIso (dualGroup G)) (hopfSpec_dualCoordinateIso_hom G)
  dsimp only [CommRingCat.carrier, CommRingCat.commRing] at h0
  dsimp only [coordinateEvaluation_second, evaluation, coordinateProductIso, bidualIso] at h0 ⊢
  exact h0

end AlgebraicGeometry.Scheme.Group.CartierDuality
