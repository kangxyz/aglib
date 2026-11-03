/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.CommonFieldSeparableCover

/-! # The original ring-map presentation of the separable pointed cover

The scalar compatibility and ambient embedding construct the same algebra map.
The cover, its mark, order bound, and zero use the unique existing supplier.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u
attribute [local instance] hasSheafifyLarge HasExt.standard
open FiniteEtale

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {U : Scheme.{u}} (p : U ⟶ Spec (.of k))

variable (F C E : Type u) [Field F] [Field C] [Field E]
  [Algebra k F] [Module.Finite k F]
  [Algebra k C] [Algebra K C] [IsScalarTower k K C]
  [Algebra C E] [Algebra K E] [IsScalarTower K C E]
  [Algebra k E] [IsScalarTower k K E] [Module.Finite K E]
  (aC : F →ₐ[k] C)
  (Ω : Type u) [Field Ω] [Algebra C Ω] (j : E →ₐ[C] Ω)
  (i : F →+* E)
  (hi₁ : j.toRingHom.comp i = (algebraMap C Ω).comp aC.toRingHom)
  (hi₂ : i.comp (algebraMap k F) = (algebraMap K E).comp (algebraMap k K))
  [CompactSpace U] [QuasiSeparatedSpace U] [GeometricallyConnected p]

local instance : ConnectedSpace (pullback p (Spec.algebraMap k F) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap k F))
local instance : ConnectedSpace
    (pullback p (Spec.algebraMap k (separableClosure k F)) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton
    (pullback.snd p (Spec.algebraMap k (separableClosure k F)))

include hi₁ hi₂ in
/-- Promote the actual ring map before instantiating finite-stage field carriers. -/
theorem exists_commonScalar_ring_separable_cover_and_zero
    (x : Spec (.of k) ⟶ U) (hx : x ≫ p = 𝟙 _)
    {V : Scheme.{u}} [ConnectedSpace V]
    (aV : V ⟶ U) (qV : V ⟶ Spec (.of F))
    (H : IsPullback aV qV p (Spec.algebraMap k F))
    (Y : FiniteEtale V) [IsGalois Y]
    (zF : Spec (.of F) ⟶ Y.obj.left)
    (hz₁ : zF ≫ Y.obj.hom ≫ aV = Spec.algebraMap k F ≫ x)
    (hz₂ : zF ≫ Y.obj.hom ≫ qV = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A] (degree n : ℕ)
    (hcard : Nat.card (Aut Y) ∣ n)
    (ξ : Sheaf.H.{u + 2} (ConstantFinite.coefficient A
      (pullback p (Spec.algebraMap k K))) degree)
    (hzero :
      let q := Y.obj.hom ≫ qV
      let a := Y.obj.hom ≫ aV
      let ha : a ≫ p = q ≫ Spec.algebraMap k F :=
        (Category.assoc Y.obj.hom aV p).trans
          ((congrArg (fun z => Y.obj.hom ≫ z) H.w).trans
            (Category.assoc Y.obj.hom qV (Spec.algebraMap k F)).symm)
      let bC := Spec.map (CommRingCat.ofHom aC.toRingHom)
      Curves.constantRestriction A
        (pullback.snd (Spec.algebraMap C E) (pullback.snd q bC) ≫
          scalarClassMap p q a (Spec.algebraMap k F) ha bC
            (Spec.algebraMap K C) (Spec.algebraMap k K)
            (commonScalarSquare k K F C aC)) degree ξ = 0) :
    ∃ aE : F →ₐ[k] E, aE.toRingHom = i ∧
    ∃ Z : FiniteEtale (pullback p (Spec.algebraMap k (separableClosure k F))),
      IsGalois Z ∧ Nat.card (Aut Z) ∣ n ∧
      ∃ z : Spec (.of (separableClosure k F)) ⟶ Z.obj.left,
        z ≫ Z.obj.hom = separableSourcePoint k F p x hx ∧
        Curves.constantRestriction A
          (((baseChange (pullback.fst
            (pullback.snd p (Spec.algebraMap k (separableClosure k F)))
            (Spec.map (CommRingCat.ofHom
              (separableSourceMap k F K E aE).toRingHom)))).obj Z).obj.hom ≫
              separableFieldClassMap k K p F E aE) degree ξ = 0 := by
  let aE : F →ₐ[k] E :=
    { i with
      commutes' := fun z => (RingHom.congr_fun hi₂ z).trans
        (IsScalarTower.algebraMap_apply k K E z).symm }
  have haE : (algebraMap C E).comp aC.toRingHom = aE.toRingHom := by
    apply RingHom.ext
    intro z
    apply j.injective
    exact (j.commutes (aC z)).trans (RingHom.congr_fun hi₁ z).symm
  obtain ⟨Z, hZ, hcardZ, z, hz, hzeroZ⟩ :=
    exists_commonScalar_separable_cover_and_zero k K p F C E aC aE haE
      x hx aV qV H Y zF hz₁ hz₂ A degree n hcard ξ hzero
  exact ⟨aE, rfl, Z, hZ, hcardZ, z, hz, hzeroZ⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
