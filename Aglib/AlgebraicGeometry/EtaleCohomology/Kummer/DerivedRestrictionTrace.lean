/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.MixedEdgeBoundary
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedAdjointBoundary
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.DerivedRestrictionMarked

/-! The signed trace on the original marked Kummer restriction. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open DerivedCategory Picard RepresentedKernel
open CategoryTheory.Abelian

universe u dX dS w s e v

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory

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
  {K G : Grp (Over S)} {q : G ⟶ G} [IsCommMonObj K.X] [IsCommMonObj G.X]
  (m : KernelMarking K G G q) (hpow : representedSheafMap q = n • 𝟙 (representedSheaf G))
  (j : representedSheaf G ⟶ normalizedPicardEtaleSheaf p o ho)

set_option hygiene false in
local notation "A" => AbelianSheaf.{u, u + 1} S
set_option hygiene false in
local notation "B" => AbelianSheaf.{u, u + 1} X
set_option hygiene false in
local notation "H₁" => Plus.homologyFunctor A 1
set_option hygiene false in
local notation "F" => Plus.singleFunctor A 0
set_option hygiene false in
local notation "U" => (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
  (AddCommGrpCat.of (ULift.{u + 1} ℤ))
set_option hygiene false in
local notation "V₁" => Plus.singleFunctorCompHomologyFunctorIso (C := A) 1

set_option hygiene false in
local notation "T" => derivedKummerTriangle p n hn (levelInvertible p n hi)

set_option hygiene false in
local notation "P" => normalizedPicardEtaleSheaf p o ho

set_option hygiene false in
local notation "eT" => derivedKummerH1KernelIso.{u, dX, dS, w, s, e}
  p n hn (levelInvertible p n hi) o ho

/-- The original marked kernel in the original first Kummer homology. -/
abbrev markedKummerH1Map :
    representedSheaf K ⟶ (H₁).obj (T).obj₁ :=
  let k := kernel.map (n • 𝟙 (representedSheaf G)) (n • 𝟙 P) j j (by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
        Category.id_comp, Category.comp_id])
  (markedPowerKernelIso m n hpow).hom ≫ k ≫ (eT).inv.τ₁

/-- The original marked map retains the kernel inclusion in the original Picard homology. -/
theorem markedKummerH1Map_comp_inclusion :
    markedKummerH1Map p o ho n hn hi m hpow j ≫ (H₁).map (T).mor₁ ≫ (eT).hom.τ₂ =
      (markedKernelSequence m).f ≫ j := by
  let H := H₁
  let V := H.obj (T).obj₁
  let J := representedSheaf G
  let e₁ : V ≅ kernel (n • 𝟙 P) := (ShortComplex.π₁ (C := A)).mapIso (eT)
  let q : H.obj (T).obj₂ ⟶ P := (eT).hom.τ₂
  let k := kernel.map (n • 𝟙 J) (n • 𝟙 P) j j (by
    simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
        Category.id_comp, Category.comp_id])
  let i := kernel.ι (n • 𝟙 P)
  let eK := markedPowerKernelIso m n hpow
  have hκ : H.map (T).mor₁ ≫ q = e₁.hom ≫ i :=
    (derivedKummerH1KernelIso_inclusion p n hn (levelInvertible p n hi) o ho).symm
  have hk : k ≫ i = kernel.ι (n • 𝟙 J) ≫ j := kernel.lift_ι _ _ _
  change (eK.hom ≫ k ≫ e₁.inv) ≫ H.map (T).mor₁ ≫ q = _
  rw [hκ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hk, ← Category.assoc eK.hom, markedPowerKernelIso_hom_ι]

/-- Testing the given degree-one class in the original Picard sheaf detects
its original marked kernel value. -/
theorem markedKummerH1Map_value_of_mapped {W : A}
    (x : (Plus.singleFunctor A 1).obj W ⟶ (T).obj₁) (a : W ⟶ representedSheaf K)
    (hx : (H₁).map (x ≫ (T).mor₁) ≫ (eT).hom.τ₂ =
      (V₁).hom.app W ≫ a ≫ (markedKernelSequence m).f ≫ j) :
    (H₁).map x = (V₁).hom.app W ≫ a ≫ markedKummerH1Map p o ho n hn hi m hpow j := by
  let H := H₁
  let f := (T).mor₁
  let e₁ : H.obj (T).obj₁ ≅ kernel (n • 𝟙 P) := (ShortComplex.π₁ (C := A)).mapIso (eT)
  let q : H.obj (T).obj₂ ⟶ P := (eT).hom.τ₂
  let s := H.map f ≫ q
  let i := kernel.ι (n • 𝟙 P)
  have hs : s = e₁.hom ≫ i :=
    (derivedKummerH1KernelIso_inclusion p n hn (levelInvertible p n hi) o ho).symm
  let : Mono s := (congrArg Mono hs).mpr inferInstance
  apply (cancel_mono s).mp
  let a' := (V₁).hom.app W ≫ a
  let j' := markedKummerH1Map p o ho n hn hi m hpow j
  have h₀ : H.map x ≫ s = H.map (x ≫ f) ≫ q := by
    exact (Category.assoc (H.map x) (H.map f) q).symm.trans
      (congrArg (fun g => g ≫ q) (H.map_comp x f).symm)
  have h₁ : j' ≫ s = (markedKernelSequence m).f ≫ j :=
    markedKummerH1Map_comp_inclusion p o ho n hn hi m hpow j
  change H.map x ≫ s = (a' ≫ j') ≫ s
  calc
    _ = H.map (x ≫ f) ≫ q := h₀
    _ = a' ≫ (markedKernelSequence m).f ≫ j := hx.trans (Category.assoc _ _ _).symm
    _ = a' ≫ (j' ≫ s) := congrArg (fun g => a' ≫ g) h₁.symm
    _ = _ := (Category.assoc _ _ _).symm

/-- The original shifted trace gives a coefficient functional on the original marked kernel. -/
abbrev markedKummerTraceFunctional {V : A}
    (t : ShiftedHom (T).obj₁ ((F).obj V) (-1 : ℤ)) :=
  let η := (Plus.singleFunctors A).shiftIso (-1) 1 0 (by omega)
  markedKummerH1Map p o ho n hn hi m hpow j ≫ (H₁).map (t ≫ η.hom.app V) ≫ (V₁).hom.app V

variable [HasExt.{v} A] [Epi (n • 𝟙 (representedSheaf G))]

/-- The original relative Kummer boundary evaluates as the negative original marked
extension with the traced coefficient map. -/
theorem markedKummer_trace_boundary {V : A}
    (c : Sheaf.H.{w} (gm X) 1) (a : U ⟶ representedSheaf G)
    (t : ShiftedHom (T).obj₁ ((F).obj V) (-1 : ℤ)) (y : Ext.{v} U V 1)
    (hc :
      let ep := ((higherDirectImageIso p 1).app (gm X)).symm ≪≫
        gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho
      (H₁).map (cohomologyOriginalDerivedAdjunct p (gm X) c) =
        (V₁).hom.app U ≫ a ≫ j ≫ ep.inv)
    (hy :
      let M := (Plus.singleFunctor B 0).obj (mu X n)
      let eInt := ((inverseImage p).rightDerivedFunctorPlusSingleIso 0).app U ≪≫
        (Plus.singleFunctor B 0).mapIso
          ((inverseImageConstantIso p).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      let z := (derivedImageAdjunction p).shiftedHomEquiv 2 ((F).obj U) M
        (eInt.hom ≫ (boundary X n hn (levelInvertible p n hi) 1 c).homPlus)
      y.homPlus = z.comp t (by omega : (-1 : ℤ) + 2 = 1)) :
    y = -(((Ext.mk₀ a).comp (markedPowerKernelSequence_shortExact m n hpow).extClass
        (zero_add 1)).comp (Ext.mk₀ (markedKummerTraceFunctional p o ho n hn hi m hpow j t))
          (add_zero 1)) := by
  obtain ⟨B₀, b, eB, F₀, i₀, δ₀, f, eF, _, hB, hF, _, hdist, _, _, hδ, hfirst, ha, lift⟩ :=
    exists_derivedKummerRestriction p o ho n hn hi (representedSheaf G) j
  let : B₀.IsLE 1 := hB
  let : F₀.IsLE 1 := hF
  let x := cohomologyOriginalDerivedAdjunct p (gm X) c
  have hca : (H₁).map x = (V₁).hom.app U ≫ a ≫
      (j ≫ (((higherDirectImageIso p 1).app (gm X)).symm ≪≫
        gmHigherDirectImageNormalizedPicardIso.{u, w, s, e} p o ho).inv) := hc
  obtain ⟨x₀, hx₀, hx₁⟩ := lift x a hca
  let T₀ := Triangle.mk i₀ (n • 𝟙 B₀) δ₀
  let : T₀.obj₁.IsLE 1 := hF
  let : T₀.obj₂.IsLE 1 := hB
  let : T₀.obj₃.IsLE 1 := hB
  let eFm := markedMultiplicationFibreH1Iso m n hpow eF
  let eK := markedPowerKernelIso m n hpow
  let θ := markedKummerTraceFunctional p o ho n hn hi m hpow j t
  let η := (Plus.singleFunctors A).shiftIso (-1) 1 0 (by omega)
  let α := (H₁).map (t ≫ η.hom.app V) ≫ (V₁).hom.app V
  let ι := markedKummerH1Map p o ho n hn hi m hpow j
  have hι : (H₁).map f = eFm.hom ≫ ι := by
    let k := kernel.map (n • 𝟙 (representedSheaf G)) (n • 𝟙 P) j j (by
      simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
        Category.id_comp, Category.comp_id])
    let L := (H₁).obj (T).obj₁
    let f₁ : L ⟶ kernel (n • 𝟙 P) := (eT).hom.τ₁
    let f₂ : kernel (n • 𝟙 P) ⟶ L := (eT).inv.τ₁
    have he : f₁ ≫ f₂ = 𝟙 L :=
      congrArg (fun b => b.τ₁) (eT).hom_inv_id
    have hf := congrArg (fun a => a ≫ f₂) ha
    change ((H₁).map f ≫ f₁) ≫ f₂ = (eF.hom ≫ k) ≫ f₂ at hf
    have heK : eFm.hom ≫ eK.hom = eF.hom := by
      change (eF.hom ≫ eK.inv) ≫ eK.hom = _
      rw [Category.assoc, eK.inv_hom_id, Category.comp_id]
    calc
      _ = (H₁).map f ≫ (f₁ ≫ f₂) :=
        ((congrArg (fun g : L ⟶ L => (H₁).map f ≫ g) he).trans (Category.comp_id _)).symm
      _ = ((H₁).map f ≫ f₁) ≫ f₂ := (Category.assoc _ _ _).symm
      _ = (eF.hom ≫ k) ≫ f₂ := hf
      _ = _ := by
        change (eF.hom ≫ k) ≫ f₂ = eFm.hom ≫ eK.hom ≫ k ≫ f₂
        rw [← Category.assoc eFm.hom eK.hom, heK, Category.assoc]
  have ht : (H₁).map (f ≫ t ≫ η.hom.app V) ≫ (V₁).hom.app V = eFm.hom ≫ θ := by
    change (H₁).map (f ≫ (t ≫ η.hom.app V)) ≫ (V₁).hom.app V = eFm.hom ≫ (ι ≫ α)
    rw [(H₁).map_comp, Category.assoc, hι]
    exact Category.assoc _ _ _
  let adj : shiftFunctor (Plus A) (-1 : ℤ) ⊣ shiftFunctor (Plus A) (1 : ℤ) :=
    (shiftEquiv' (Plus A) (-1 : ℤ) 1 (by omega)).toAdjunction
  let z : ShiftedHom ((F).obj U) (T).obj₃ (1 : ℤ) :=
    adj.homEquiv ((F).obj U) (T).obj₃ (η.hom.app U ≫ x)
  have hz : z = adj.homEquiv ((F).obj U) (T).obj₃ (η.hom.app U ≫ x₀ ≫ b) :=
    congrArg (fun g => adj.homEquiv ((F).obj U) (T).obj₃ (η.hom.app U ≫ g)) hx₀.symm
  have hY : y.homPlus = (z.comp ((T).mor₃ : ShiftedHom (T).obj₃ (T).obj₁ (1 : ℤ))
      (by omega : 1 + 1 = (2 : ℤ))).comp t (by omega : (-1 : ℤ) + 2 = 1) :=
    hy.trans (congrArg (fun z' => z'.comp t (by omega : (-1 : ℤ) + 2 = 1))
      (derivedKummerTriangle_originalAdjunct_boundary p n hn (levelInvertible p n hi) c))
  exact Plus.mixedEdgeTrace_boundary_of_comparison T₀ hdist
    (markedPowerKernelSequence_shortExact m n hpow) eFm.hom eB.hom eB.hom
    (markedMultiplicationFibreH1_first_square m n hpow i₀ eB eF hfirst)
    (markedMultiplicationFibreH1_second_square m n hpow eB) x₀ a hx₁
    f b (T).mor₃ hδ.symm θ t ht z hz y hY

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
