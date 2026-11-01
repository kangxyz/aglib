/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Descent.Integrality
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Canonical normalization base change through a filtered colimit

If the original normalization comparison is bijective at every stage of a
filtered diagram of algebras, the canonical comparison is bijective at its
actual colimit. Tensor cocones are the native tensor-product functor, via its
pushout adjunction. Kernel elements and monic integral witnesses descend to
actual stages. No smoothness or flatness of the colimit is assumed and no
colimit of replacement normalization objects is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace integralClosure

variable (R B A : Type u) [CommRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra R A]

/-- The original normalization inclusion tensored on the right. This is the
native tensor map, with the factors reversed only for the existing tensor functor. -/
def flippedTensorInclusion : integralClosure R B ⊗[R] A →ₐ[R] B ⊗[R] A :=
  Algebra.TensorProduct.map (integralClosure R B).val (AlgHom.id R A)

/-- Native tensor symmetry compares the ambient value of the canonical
normalization map with the reversed-factor tensor inclusion. -/
theorem flippedTensorInclusion_comm (x : A ⊗[R] integralClosure R B) :
    flippedTensorInclusion R B A (Algebra.TensorProduct.comm R A (integralClosure R B) x) =
      Algebra.TensorProduct.comm R A B ((TensorProduct.toIntegralClosure R A B x).val) := by
  change (Algebra.TensorProduct.map (integralClosure R B).val (AlgHom.id R A))
      (Algebra.TensorProduct.comm R A (integralClosure R B) x) =
    Algebra.TensorProduct.comm R A B
      (Algebra.TensorProduct.map (AlgHom.id R A) (integralClosure R B).val x)
  exact (Algebra.TensorProduct.comm_comp_map_apply (AlgHom.id R A)
    (integralClosure R B).val x).symm

/-- Naturality is the whole native tensor-map composition law. -/
theorem flippedTensorInclusion_naturality
    {A' : Type u} [CommRing A'] [Algebra R A'] (f : A →ₐ[R] A')
    (x : integralClosure R B ⊗[R] A) :
    Algebra.TensorProduct.map (AlgHom.id R B) f (flippedTensorInclusion R B A x) =
      flippedTensorInclusion R B A'
        (Algebra.TensorProduct.map (AlgHom.id R (integralClosure R B)) f x) := by
  have h : (Algebra.TensorProduct.map (AlgHom.id R B) f).comp
        (flippedTensorInclusion R B A) =
      (flippedTensorInclusion R B A').comp
        (Algebra.TensorProduct.map (AlgHom.id R (integralClosure R B)) f) := by
    simp only [flippedTensorInclusion, ← Algebra.TensorProduct.map_comp,
      AlgHom.id_comp, AlgHom.comp_id]
  exact congrArg (fun g => g x) h

/-- Integrality relative to the original right tensor inclusion is precisely
integrality in the usual left-oriented tensor algebra after native symmetry. -/
theorem integralElem_includeRight_iff (x : B ⊗[R] A) :
    (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom.IsIntegralElem x ↔
      IsIntegral A (Algebra.TensorProduct.comm R B A x) := by
  have h : (Algebra.TensorProduct.comm R B A).toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom =
      algebraMap A (A ⊗[R] B) := by ext a; rfl
  change
    (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom.IsIntegralElem x ↔
    (algebraMap A (A ⊗[R] B)).IsIntegralElem
      ((Algebra.TensorProduct.comm R B A).toRingHom x)
  rw [← h]
  exact (RingHom.IsIntegralElem.map_iff
      (f := (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom)
      (g := (Algebra.TensorProduct.comm R B A).toRingHom)
      (Algebra.TensorProduct.comm R B A).injective (x := x)).symm

/-- Bijectivity of the canonical comparison is exactly injectivity of its
ambient tensor map and lifting of the actual integral elements. -/
theorem toIntegralClosure_bijective_iff_flipped :
    Function.Bijective (TensorProduct.toIntegralClosure R A B) ↔
      Function.Injective (flippedTensorInclusion R B A) ∧
      ∀ y : B ⊗[R] A,
        (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom.IsIntegralElem y →
        ∃ x, flippedTensorInclusion R B A x = y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨x, rfl⟩ := (Algebra.TensorProduct.comm R A (integralClosure R B)).surjective x
      obtain ⟨y, rfl⟩ := (Algebra.TensorProduct.comm R A (integralClosure R B)).surjective y
      apply congrArg (Algebra.TensorProduct.comm R A (integralClosure R B))
      apply h.injective
      apply Subtype.ext
      apply (Algebra.TensorProduct.comm R A B).injective
      simpa only [flippedTensorInclusion_comm] using hxy
    · intro y hy
      let z : integralClosure A (A ⊗[R] B) :=
        ⟨Algebra.TensorProduct.comm R B A y, (integralElem_includeRight_iff R B A y).mp hy⟩
      obtain ⟨x, hx⟩ := h.surjective z
      refine ⟨Algebra.TensorProduct.comm R A (integralClosure R B) x, ?_⟩
      rw [flippedTensorInclusion_comm, hx]
      exact (Algebra.TensorProduct.comm R A B).apply_symm_apply y
  · rintro ⟨hi, hs⟩
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply (Algebra.TensorProduct.comm R A (integralClosure R B)).injective
      apply hi
      rw [flippedTensorInclusion_comm, flippedTensorInclusion_comm, hxy]
    · intro z
      let y := Algebra.TensorProduct.comm R A B z.val
      have hy :
          (Algebra.TensorProduct.includeRight : A →ₐ[R] B ⊗[R] A).toRingHom.IsIntegralElem
          y := by
        apply (integralElem_includeRight_iff R B A y).mpr
        change IsIntegral A (Algebra.TensorProduct.comm R B A
          (Algebra.TensorProduct.comm R A B z.val))
        rw [← Algebra.TensorProduct.comm_symm (R := R) (A := A) (B := B),
          AlgEquiv.symm_apply_apply]
        exact z.property
      obtain ⟨x, hx⟩ := hs y hy
      let x' := Algebra.TensorProduct.comm R (integralClosure R B) A x
      refine ⟨x', ?_⟩
      apply Subtype.ext
      apply (Algebra.TensorProduct.comm R A B).injective
      rw [← flippedTensorInclusion_comm]
      have hback : Algebra.TensorProduct.comm R A (integralClosure R B) x' = x := by
        dsimp only [x']
        rw [← Algebra.TensorProduct.comm_symm (R := R) (A := integralClosure R B) (B := A),
          AlgEquiv.symm_apply_apply]
      exact (congrArg (flippedTensorInclusion R B A) hback).trans hx

end integralClosure

namespace TensorProduct

/-- Stagewise bijectivity of the canonical normalization comparison passes to
the actual filtered colimit. The original coefficient and tensor maps are used
throughout; no smoothness or flatness of the colimit is an input. -/
theorem toIntegralClosure_bijective_of_isColimit
    (R B : CommRingCat.{u}) [Algebra R B]
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (F : I ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (hstage : ∀ i, Function.Bijective (toIntegralClosure R (F.obj i) B)) :
    Function.Bijective (toIntegralClosure R c.pt B) := by
  let : IsConnected I := IsFiltered.isConnected I
  let C : CommRingCat := .of (integralClosure R B)
  let : PreservesColimits (CommRingCat.tensorProd R B) :=
    preservesColimits_of_natIso (CommRingCat.tensorProdIsoPushout R B).symm
  let : PreservesColimits (CommRingCat.tensorProd R C) :=
    preservesColimits_of_natIso (CommRingCat.tensorProdIsoPushout R C).symm
  let F₀ := F ⋙ Under.forget R
  let G := F ⋙ CommRingCat.tensorProd R B ⋙ Under.forget B
  let H := F ⋙ CommRingCat.tensorProd R C ⋙ Under.forget C
  let cF := (Under.forget R).mapCocone c
  let cG := (CommRingCat.tensorProd R B ⋙ Under.forget B).mapCocone c
  let cH := (CommRingCat.tensorProd R C ⋙ Under.forget C).mapCocone c
  have hF : IsColimit cF := isColimitOfPreserves (Under.forget R) hc
  have hG : IsColimit cG := isColimitOfPreserves
    (CommRingCat.tensorProd R B ⋙ Under.forget B) hc
  have hH : IsColimit cH := isColimitOfPreserves
    (CommRingCat.tensorProd R C ⋙ Under.forget C) hc
  let η : F₀ ⟶ G :=
    { app i := CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : F.obj i →ₐ[R] B ⊗[R] F.obj i).toRingHom
      naturality i j f := by ext x; rfl }
  let φ : cF.pt ⟶ cG.pt := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : c.pt →ₐ[R] B ⊗[R] c.pt).toRingHom
  have hφ : ∀ i, cF.ι.app i ≫ φ = η.app i ≫ cG.ι.app i := by intro i; ext x; rfl
  let N (A : Under R) := integralClosure.flippedTensorInclusion R B A
  have hnι (i : I) (x : H.obj i) :
      (cG.ι.app i).hom (N (F.obj i) x) = N c.pt ((cH.ι.app i).hom x) :=
    integralClosure.flippedTensorInclusion_naturality R B (F.obj i)
      (CommRingCat.toAlgHom (c.ι.app i)) x
  have hnm {i j : I} (f : i ⟶ j) (x : H.obj i) :
      (G.map f).hom (N (F.obj i) x) = N (F.obj j) ((H.map f).hom x) :=
    integralClosure.flippedTensorInclusion_naturality R B (F.obj i)
      (CommRingCat.toAlgHom (F.map f)) x
  have hN (i : I) :=
    (integralClosure.toIntegralClosure_bijective_iff_flipped R B (F.obj i)).mp (hstage i)
  apply (integralClosure.toIntegralClosure_bijective_iff_flipped R B c.pt).mpr
  constructor
  · apply (injective_iff_map_eq_zero (N c.pt).toRingHom).mpr
    intro x hx
    obtain ⟨i, x, rfl⟩ := Concrete.isColimit_exists_rep H hH x
    have hz : (cG.ι.app i).hom (N (F.obj i) x) = (cG.ι.app i).hom 0 := by
      exact (hnι i x).trans (hx.trans ((cG.ι.app i).hom.map_zero).symm)
    obtain ⟨j, f, g, hfg⟩ := (Concrete.isColimit_rep_eq_iff_exists G hG _ _).mp hz
    have hj : N (F.obj j) ((H.map f).hom x) = 0 := by
      exact (hnm f x).symm.trans (hfg.trans ((G.map g).hom.map_zero))
    have hxj : (H.map f).hom x = 0 := (hN j).1 (hj.trans (map_zero (N (F.obj j))).symm)
    calc
      (cH.ι.app i).hom x = (cH.ι.app j).hom ((H.map f).hom x) :=
        (ConcreteCategory.congr_hom (cH.w f) x).symm
      _ = 0 := (congrArg (cH.ι.app j).hom hxj).trans ((cH.ι.app j).hom.map_zero)
  · intro y hy
    obtain ⟨i, y, rfl⟩ := Concrete.isColimit_exists_rep G hG y
    obtain ⟨j, f, hj⟩ :=
      (CommRingCat.isIntegralElem_iff_exists_stage F₀ G η cF cG hF hG φ hφ i y).mp hy
    obtain ⟨x, hx⟩ := (hN j).2 ((G.map f).hom y) hj
    let xj : H.obj j := x
    have hxj : N (F.obj j) xj = (G.map f).hom y := hx
    refine ⟨(cH.ι.app j).hom xj, ?_⟩
    exact (hnι j xj).symm.trans ((congrArg (cG.ι.app j).hom hxj).trans
      (ConcreteCategory.congr_hom (cG.w f) y))

end TensorProduct
