/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Fibre
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedH1Kernel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ProperGmDirectImage
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure

/-! The original Kummer comparison of the restricted Picard fibre. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open DerivedCategory Picard

universe u dX dS w s e

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange p).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
  (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(S, ⊤)))
  (J : AbelianSheaf.{u, u + 1} S) (j : J ⟶ normalizedPicardEtaleSheaf p o ho)
  [Epi (n • 𝟙 J)]

/-- The original relative Kummer fibre receives the original multiplication
fibre of the specified Picard restriction, preserving both connecting maps. -/
theorem exists_derivedKummerRestriction :
    let A := AbelianSheaf.{u, u + 1} S
    let H₀ := Plus.homologyFunctor A 0
    let H₁ := Plus.homologyFunctor A 1
    let T := derivedKummerTriangle p n hn (levelInvertible p n hi)
    let P := normalizedPicardEtaleSheaf p o ho
    let ep := ((higherDirectImageIso p 1).app (gm X)).symm ≪≫
      gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho
    let ι := j ≫ ep.inv
    let eT := derivedKummerH1KernelIso.{u, dX, dS, w, s, e}
      p n hn (levelInvertible p n hi) o ho
    let τ₁ : H₁.obj T.obj₁ ⟶ kernel (n • 𝟙 P) := eT.hom.τ₁
    let k := kernel.map (n • 𝟙 J) (n • 𝟙 P) j j (by
      simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp,
        Category.comp_id])
    ∃ (B₀ : Plus A) (b : B₀ ⟶ T.obj₂) (eB : H₁.obj B₀ ≅ J)
      (F₀ : Plus A) (i₀ : F₀ ⟶ B₀) (δ₀ : B₀ ⟶ F₀⟦(1 : ℤ)⟧)
      (a : F₀ ⟶ T.obj₁) (eF : H₁.obj F₀ ≅ kernel (n • 𝟙 J)),
      B₀.IsGE 0 ∧ B₀.IsLE 1 ∧ F₀.IsLE 1 ∧ IsIso (H₀.map b) ∧
      Triangle.mk i₀ (n • 𝟙 B₀) δ₀ ∈ distTriang (Plus A) ∧
      H₁.map b = eB.hom ≫ ι ∧
      i₀ ≫ b = a ≫ T.mor₁ ∧ δ₀ ≫ a⟦(1 : ℤ)⟧' = b ≫ T.mor₃ ∧
      eF.hom ≫ kernel.ι (n • 𝟙 J) = H₁.map i₀ ≫ eB.hom ∧
      H₁.map a ≫ τ₁ = eF.hom ≫ k ∧
      ∀ {W : A} (x : (Plus.singleFunctor A 1).obj W ⟶ T.obj₂) (f : W ⟶ J),
        H₁.map x = (Plus.singleFunctorCompHomologyFunctorIso (C := A) 1).hom.app W ≫ f ≫ ι →
        ∃ x₀ : (Plus.singleFunctor A 1).obj W ⟶ B₀,
          x₀ ≫ b = x ∧ H₁.map x₀ ≫ eB.hom =
            (Plus.singleFunctorCompHomologyFunctorIso (C := A) 1).hom.app W ≫ f := by
  intro A H₀ H₁ T P ep ι eT τ₁ k
  let τ₂ : H₁.obj T.obj₂ ⟶ P := eT.hom.τ₂
  let K := T.obj₂
  let M := (Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj (gm X)
  let : K.IsGE 0 := (directImage p).rightDerivedFunctorPlus_isGE M 0
  obtain ⟨B₀, b, eB, hge, hle, h₀, h₁, hlift⟩ := Plus.exists_postnikovRestriction K ι
  let : B₀.IsLE 1 := hle
  have hp := epi_derivedDirectImage_homologyZero_power p n hn hi
  have hpow : T.mor₂ = n • 𝟙 K := derivedKummerTriangle_mor₂ p n hn (levelInvertible p n hi)
  let : Epi (n • 𝟙 (H₀.obj K)) := by
    have hp' : Epi (H₀.map (n • 𝟙 K)) :=
      (congrArg (fun f : K ⟶ K => Epi (H₀.map f)) hpow).mp hp
    have h : H₀.map (n • 𝟙 K) = n • 𝟙 (H₀.obj K) :=
      (show H₀.map (n • 𝟙 K) = n • H₀.map (𝟙 K) from H₀.map_nsmul).trans
        (congrArg (fun f => n • f) (H₀.map_id K))
    exact (congrArg Epi h).mp hp'
  have ht : Triangle.mk T.mor₁ (n • 𝟙 K) T.mor₃ ∈ distTriang (Plus A) := by
    rw [← hpow]
    exact derivedKummerTriangle_distinguished p n hn (levelInvertible p n hi)
  obtain ⟨F₀, i₀, δ₀, a, eF, hleF, hT₀, hi₀, hδ, hF⟩ :=
    Plus.exists_postnikovMultiplicationFibre_comparison b eB h₀ n T.mor₁ T.mor₃ ht
  have he : τ₂ = ep.hom :=
    derivedKummerH1KernelIso_hom_τ₂ p n hn (levelInvertible p n hi) o ho
  have hm : H₁.map a ≫ H₁.map T.mor₁ = H₁.map i₀ ≫ H₁.map b := by
    rw [← H₁.map_comp, ← hi₀, H₁.map_comp]
  have hb : H₁.map b ≫ ep.hom = eB.hom ≫ j := by
    rw [h₁]
    change (eB.hom ≫ j ≫ ep.inv) ≫ ep.hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hk : k ≫ kernel.ι (n • 𝟙 P) = kernel.ι (n • 𝟙 J) ≫ j := by
    dsimp only [k, kernel.map]
    exact kernel.lift_ι _ _ _
  have hcomm : H₁.map a ≫ τ₁ = eF.hom ≫ k := by
    let kP := kernel.ι (n • 𝟙 P)
    let kJ := kernel.ι (n • 𝟙 J)
    apply (cancel_mono kP).mp
    have ht : τ₁ ≫ kP = H₁.map T.mor₁ ≫ τ₂ :=
      derivedKummerH1KernelIso_inclusion p n hn (levelInvertible p n hi) o ho
    calc
      _ = H₁.map a ≫ (τ₁ ≫ kP) := Category.assoc _ _ _
      _ = H₁.map a ≫ (H₁.map T.mor₁ ≫ ep.hom) :=
        congrArg (fun z => H₁.map a ≫ z)
          (ht.trans (congrArg (fun z => H₁.map T.mor₁ ≫ z) he))
      _ = (H₁.map i₀ ≫ H₁.map b) ≫ ep.hom :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ ep.hom) hm)
      _ = H₁.map i₀ ≫ eB.hom ≫ j :=
        (Category.assoc _ _ _).trans (congrArg (fun z => H₁.map i₀ ≫ z) hb)
      _ = eF.hom ≫ kJ ≫ j := ((reassoc_of% hF) j).symm
      _ = _ := (congrArg (fun z => eF.hom ≫ z) hk.symm).trans (Category.assoc _ _ _).symm
  exact ⟨B₀, b, eB, F₀, i₀, δ₀, a, eF, hge, hle, hleF, h₀, hT₀,
    h₁, hi₀, hδ, hF, hcomm, hlift⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
