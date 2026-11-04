/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.PrincipalKernelComparison
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.Alternation
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.WeilPairing.RootFieldBaseChange
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Projective

/-! Descent of original Weil alternation from a line-bundle polarization. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.OverField Scheme.Group Scheme.Modules.Invertible
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

/-- Tensor pasting at the original diagonal and original restricted principal map. -/
private theorem diagonal_comp_of_tensor_baseChange
    {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal]
    {G H R : C} {G' H' R' : D} (s : G ⟶ H) (s' : G' ⟶ H')
    (u : F.obj G ⟶ G') (v : F.obj H ⟶ H') (e : F.obj R ⟶ R')
    (p : G ⊗ H ⟶ R) (p' : G' ⊗ H' ⟶ R')
    (hs : u ≫ s' = F.map s ≫ v)
    (hp : (u ⊗ₘ v) ≫ p' = Functor.LaxMonoidal.μ F G H ≫ F.map p ≫ e) :
    F.map (lift (𝟙 G) s ≫ p) ≫ e = u ≫ lift (𝟙 G') s' ≫ p' := by
  have hl : lift (𝟙 (F.obj G)) (F.map s) ≫ (u ⊗ₘ v) = u ≫ lift (𝟙 G') s' := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp only [Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
      exact hs.symm
  have hm : lift (𝟙 (F.obj G)) (F.map s) ≫ Functor.LaxMonoidal.μ F G H =
      F.map (lift (𝟙 G) s) := by
    simpa only [F.map_id] using Functor.Monoidal.lift_μ F (𝟙 G) s
  calc
    _ = lift (𝟙 (F.obj G)) (F.map s) ≫ Functor.LaxMonoidal.μ F G H ≫ F.map p ≫ e := by
      rw [F.map_comp, ← hm]
      simp only [Category.assoc]
    _ = lift (𝟙 (F.obj G)) (F.map s) ≫ (u ⊗ₘ v) ≫ p' :=
      congrArg (fun q => lift (𝟙 (F.obj G)) (F.map s) ≫ q) hp.symm
    _ = _ := by rw [← Category.assoc, hl, Category.assoc]

variable {k : Type u} [Field k] (A : Grp (FScheme k)) [IsCommMonObj A.X]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom]
  (e : A ≅ Grp.mk (picardIdentityComponent A.X.hom P R))
  (K : Type u) [Field K] [Algebra k K]

local notation "scalar" => Spec.algebraMap k K
local notation "F" => Over.pullback scalar
local notation "AK" => Functor.obj (Functor.mapGrp F) A
local notation "PK" => LocallyNoetherianOver.baseChange scalar P
local notation "RK" => baseChangeRepresentableBy A.X.hom scalar P R
local instance : LocallyOfFiniteType (PK).obj.hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd P.obj.hom scalar))
local instance : IsCommMonObj (AK).X := MultiplicationKernel.baseChange_isCommMonObj scalar A

local instance : IsHProjective (AK).X.hom :=
  inferInstanceAs (IsHProjective (pullback.snd A.X.hom scalar))
local instance : GeometricallyIntegral (AK).X.hom :=
  inferInstanceAs (GeometricallyIntegral (pullback.snd A.X.hom scalar))
local instance : Smooth (AK).X.hom := inferInstanceAs (Smooth (pullback.snd A.X.hom scalar))
local instance : IsSeparated (PK).obj.hom :=
  inferInstanceAs (IsSeparated (pullback.snd P.obj.hom scalar))

/-- The original principal pairing is alternating when the original
scalar-extended principal map is induced by an actual line bundle. -/
theorem weilPairingMorphismOfPrincipalIso_diagonal_of_fieldLineBundle
    (L : LineBundle (AK).X.left)
    (h : (F).map e.hom.hom.hom ≫ (picardIdentityComponentBaseChangeOverIso P R K).hom =
      lineBundleClassMorphismIdentityComponent (AK).X PK RK (classOf (AK).X.left L))
    (n : ℕ) (hn : 0 < n) :
    let G := MultiplicationKernel.kernelGroup A n
    MultiplicativeGroup.rootsHomEquiv (Base k) n G.X
      (lift (𝟙 G.X) (𝟙 G.X) ≫ weilPairingMorphismOfPrincipalIso A P R e n hn) = 1 := by
  let eD := picardIdentityComponentBaseChangeGroupIso P R K
  let eK := (F).mapGrp.mapIso e ≪≫ eD
  have he : eK.hom = lineBundleClassIdentityComponentGroupHom (AK).X PK RK
      (classOf (AK).X.left L) := by
    apply Grp.hom_ext
    exact h
  let G := MultiplicationKernel.kernelGroup A n
  let GK := MultiplicationKernel.kernelGroup AK n
  let E := dualMultiplicationKernel A P R n
  let EK := dualMultiplicationKernel AK PK RK n
  let S := MultiplicativeGroup.rootsGroupScheme (Base k) n
  let SK := MultiplicativeGroup.rootsGroupScheme (Base K) n
  let a := (MultiplicationKernel.baseChangeIso scalar A n).hom.hom.hom
  let b := (dualMultiplicationKernelBaseChangeIso A P R K n).hom.hom.hom
  let eR := MultiplicativeBaseChange.rootsBaseChangeIso scalar n
  let c := eR.hom.hom.hom
  let s := (principalIsoOnMultiplicationKernel A P R e n).hom.hom.hom
  let sK := (principalIsoOnMultiplicationKernel AK PK RK eK n).hom.hom.hom
  let p : G.X ⊗ E.X ⟶ S.X := weilPairingMorphism A P R n hn
  let pK : GK.X ⊗ EK.X ⟶ SK.X := weilPairingMorphism AK PK RK n hn
  let d := lift (𝟙 G.X) s ≫ p
  let dK := lift (𝟙 GK.X) sK ≫ pK
  have hs : a ≫ sK = (F).map s ≫ b :=
    congrArg (fun f => f.hom.hom) (principalIsoOnMultiplicationKernel_fieldBaseChange A P R e K n)
  have hp := weilPairingMorphism_fieldBaseChange A P R K n hn
  have hd : (F).map d ≫ c = a ≫ dK :=
    diagonal_comp_of_tensor_baseChange F s sK a b c p pK hs hp
  have hPair (E₀ G₀ Z : FScheme K) (s₀ : G₀ ⟶ E₀) (p₀ : G₀ ⊗ E₀ ⟶ Z) :
      lift (𝟙 G₀) (𝟙 G₀) ≫ ((𝟙 G₀ ⊗ₘ s₀) ≫ p₀) = lift (𝟙 G₀) s₀ ≫ p₀ := by
    have hLift : lift (𝟙 G₀) (𝟙 G₀) ≫ (𝟙 G₀ ⊗ₘ s₀) = lift (𝟙 G₀) s₀ := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ p₀) hLift)
  have hv := weilPairingMorphismOfPrincipalIso_diagonal_of_lineBundleClass AK PK RK L eK he n hn
  have hvK : MultiplicativeGroup.rootsHomEquiv (Base K) n GK.X dK = 1 := by
    have hf := hPair EK.X GK.X SK.X sK pK
    unfold dK
    exact (congrArg (MultiplicativeGroup.rootsHomEquiv (Base K) n GK.X) hf).symm.trans hv
  have hOneK := (MultiplicativeBaseChange.rootsSectionsEquiv (Base K) n GK.X).map_one
  have h1 : dK = (1 : GK.X ⟶ SK.X) :=
    (MultiplicativeBaseChange.rootsSectionsEquiv (Base K) n GK.X).injective (hvK.trans hOneK.symm)
  let : GrpObj ((F).obj S.X) := ((F).mapGrp.obj S).grp
  let I : G.X ⟶ S.X := 1
  have hF : (F).map I ≫ c = (1 : (F).obj G.X ⟶ SK.X) := by
    have hm : (F).map I = (1 : (F).obj G.X ⟶ (F).obj S.X) :=
      ((F).homMonoidHom (X := G.X) (M := S.X)).map_one
    exact (congrArg (fun f => f ≫ c) hm).trans (MonObj.one_comp c)
  have hc : (F).map d ≫ c = (F).map I ≫ c :=
    hd.trans ((congrArg (fun q => a ≫ q) h1).trans ((MonObj.comp_one a).trans hF.symm))
  let : Surjective scalar := ⟨Function.surjective_to_subsingleton scalar⟩
  let : Flat scalar := inferInstanceAs (Flat (Spec.algebraMap k K))
  let : ∀ (Z : Scheme.{u}) (g : Z ⟶ Base k), Epi (pullback.fst g scalar) :=
    fun _ g => Flat.epi_of_flat_of_surjective (pullback.fst g scalar)
  let : (F).Faithful := Over.faithful_pullback scalar
  have : Mono c := inferInstanceAs (Mono ((Grp.forget (FScheme K)).map eR.hom))
  have hd1 : d = I := (F).map_injective ((cancel_mono c).mp hc)
  have hOld : lift (𝟙 G.X) (𝟙 G.X) ≫ weilPairingMorphismOfPrincipalIso A P R e n hn = d := by
    have hLift : lift (𝟙 G.X) (𝟙 G.X) ≫ (𝟙 G.X ⊗ₘ s) = lift (𝟙 G.X) s := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    unfold weilPairingMorphismOfPrincipalIso
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ p) hLift)
  exact (congrArg (MultiplicativeGroup.rootsHomEquiv (Base k) n G.X) (hOld.trans hd1)).trans
    ((MultiplicativeBaseChange.rootsSectionsEquiv (Base k) n G.X).map_one)

end AlgebraicGeometry.Scheme.RelativePicard
