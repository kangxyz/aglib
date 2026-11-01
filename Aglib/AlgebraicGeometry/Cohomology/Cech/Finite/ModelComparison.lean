/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.Derived

/-! # Complete comparisons of the original finite Cech models

The canonical resolution lift, original truncation inclusion, and derived model
composition are constructed before specializing the scheme or its coefficients.
The standard derived worlds and original finite-model maps are unchanged.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Compose both original comparison squares before specializing their categories. -/
private theorem mapped_model_naturality
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A A' B B' : C} {P P' : D}
    {f : A ⟶ A'} {a : A ⟶ B} {a' : A' ⟶ B'} {c : B ⟶ B'}
    {b : F.obj B ⟶ P} {b' : F.obj B' ⟶ P'} {d : P ⟶ P'}
    {m : F.obj A ⟶ P} {m' : F.obj A' ⟶ P'}
    (hμ : f ≫ a' = a ≫ c) (hD : F.map c ≫ b' = b ≫ d)
    (hm : m = F.map a ≫ b) (hm' : m' = F.map a' ≫ b') :
    F.map f ≫ m' = m ≫ d := by
  rw [hm, hm']
  calc
    F.map f ≫ (F.map a' ≫ b') = F.map (f ≫ a') ≫ b' := by
      rw [F.map_comp, Category.assoc]
    _ = F.map (a ≫ c) ≫ b' := congrArg (fun t => F.map t ≫ b') hμ
    _ = F.map a ≫ (F.map c ≫ b') := by rw [F.map_comp, Category.assoc]
    _ = (F.map a ≫ b) ≫ d := by rw [hD, Category.assoc]

/-- Cancel the actual inclusion after the complete tensor-unitor rectangle. -/
private theorem tensor_unitor_of_inclusion
    {C : Type*} [Category* C] (T : C ⥤ C) (τ : T ⟶ 𝟭 C)
    {K L K' L' : C} (i : K ⟶ K') [Mono i]
    {j : L ⟶ L'} {μ : T.obj K ⟶ L} {u : L ⟶ K}
    {a : T.obj K' ⟶ L'} {b : L' ⟶ K'}
    (hu : u ≫ i = j ≫ b) (hμ : μ ≫ j = T.map i ≫ a)
    (ha : a ≫ b = τ.app K') : μ ≫ u = τ.app K := by
  apply (cancel_mono i).mp
  rw [Category.assoc, hu, ← Category.assoc, hμ, Category.assoc, ha]
  exact τ.naturality i

/-- Map the complete chain trace rectangle and cancel its original model isomorphism. -/
private theorem trace_of_mapped_model
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B K S T V : C} {P Q : D} (E : F.obj A ≅ P)
    {μ : A ⟶ B} {u : B ⟶ K} {τ : A ⟶ K} {t : K ⟶ V}
    {v : A ⟶ S} {w : S ⟶ T} {z : T ⟶ V}
    {b : F.obj B ⟶ P} {b' : F.obj K ⟶ Q} {r : P ⟶ Q} {old : Q ⟶ F.obj V}
    (hE : E.hom = F.map μ ≫ b) (hD : F.map u ≫ b' = b ≫ r)
    (hμ : μ ≫ u = τ) (ht : F.map t = b' ≫ old)
    (hv : v ≫ w ≫ z = τ ≫ t) :
    E.inv ≫ F.map v ≫ F.map w ≫ F.map z = r ≫ old := by
  apply (cancel_epi E.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [hE]
  have hv' := congrArg (fun a => F.map a) hv
  simp only [F.map_comp] at hv'
  rw [hv', ← hμ, F.map_comp, ht]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map u) b' old, hD]
  simp only [Category.assoc]

section FiniteModels

variable {R₀ : Type u} [CommRing R₀] (X₀ : Scheme.{u}) (α₀ : R₀ →+* Γ(X₀, ⊤))
  {ι₀ : Type u} (U₀ : ι₀ → X₀.Opens)

local instance : HasDerivedCategory.{u + 1} X₀.Modules := HasDerivedCategory.standard _
local instance : HasDerivedCategory.{u + 1} (ModuleCat.{u} R₀) := HasDerivedCategory.standard _

/-- Construct the actual lift between the two chosen resolutions before specialization. -/
theorem moduleFiniteCechCanonicalResolution_naturality [X₀.IsSeparated]
    {M N : X₀.Modules} [hM : M.IsQuasicoherent] [hN : N.IsQuasicoherent]
    (f : M ⟶ N) (n : ℕ) (e : ι₀ ≃ Fin (n + 1))
    (hU : ∀ i, IsAffineOpen (U₀ i)) (hcover : iSup U₀ = ⊤) :
    DerivedCategory.Q.map ((moduleFiniteCechFunctor X₀ α₀ U₀ n).map f) ≫
        (moduleFiniteCechDerivedGlobalSectionsIso X₀ α₀ U₀ N
          (injectiveResolution N) n e hU hcover).hom =
      (moduleFiniteCechDerivedGlobalSectionsIso X₀ α₀ U₀ M
          (injectiveResolution M) n e hU hcover).hom ≫
        DerivedCategory.Plus.ι.map
          ((moduleGlobalSectionsFunctorOfHom X₀ α₀).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).map f)) := by
  exact moduleFiniteCechDerivedGlobalSectionsIso_naturality X₀ α₀ U₀ M
    (injectiveResolution M) n e hU hcover
    ⟨InjectiveResolution.desc f (injectiveResolution N) (injectiveResolution M), by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero f (injectiveResolution N) (injectiveResolution M)⟩

/-- Build the complete actual finite-model naturality, including its resolution lift. -/
theorem moduleFiniteCechModelComparison_naturality [X₀.IsSeparated]
    {M N : X₀.Modules} [hM : M.IsQuasicoherent] [hN : N.IsQuasicoherent]
    (f : M ⟶ N) (n : ℕ) (e : ι₀ ≃ Fin (n + 1))
    (hU : ∀ i, IsAffineOpen (U₀ i)) (hcover : iSup U₀ = ⊤)
    {A B : CochainComplex (ModuleCat.{u} R₀) ℤ} (a : A ⟶ B)
    (μ : A ≅ moduleFiniteCechComplex X₀ α₀ U₀ M n)
    (ν : B ≅ moduleFiniteCechComplex X₀ α₀ U₀ N n)
    (hμ : a ≫ ν.hom = μ.hom ≫ (moduleFiniteCechFunctor X₀ α₀ U₀ n).map f) :
    DerivedCategory.Q.map a ≫
        (DerivedCategory.Q.mapIso ν ≪≫ moduleFiniteCechDerivedGlobalSectionsIso
          X₀ α₀ U₀ N (injectiveResolution N) n e hU hcover).hom =
      (DerivedCategory.Q.mapIso μ ≪≫ moduleFiniteCechDerivedGlobalSectionsIso
          X₀ α₀ U₀ M (injectiveResolution M) n e hU hcover).hom ≫
        DerivedCategory.Plus.ι.map
          ((moduleGlobalSectionsFunctorOfHom X₀ α₀).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).map f)) :=
  mapped_model_naturality DerivedCategory.Q hμ
    (moduleFiniteCechCanonicalResolution_naturality X₀ α₀ U₀ f n e hU hcover) rfl rfl

/-- Construct the actual monic truncation inclusion and cancel the whole unitor rectangle. -/
theorem moduleFiniteCechModelComparison_unitor
    (M N : X₀.Modules) (f : N ⟶ M) (n : ℕ)
    (T : CochainComplex (ModuleCat.{u} R₀) ℤ ⥤ CochainComplex (ModuleCat.{u} R₀) ℤ)
    (τ : T ⟶ 𝟭 _)
    {μ : T.obj (moduleFiniteCechComplex X₀ α₀ U₀ M n) ⟶
      moduleFiniteCechComplex X₀ α₀ U₀ N n}
    {a : T.obj (moduleCechIntComplex X₀ α₀ U₀ M) ⟶ moduleCechIntComplex X₀ α₀ U₀ N}
    (hμ : μ ≫ moduleFiniteCechInclusion X₀ α₀ U₀ N n =
      T.map (moduleFiniteCechInclusion X₀ α₀ U₀ M n) ≫ a)
    (ha : a ≫ (moduleCechIntFunctor X₀ α₀ U₀).map f =
      τ.app (moduleCechIntComplex X₀ α₀ U₀ M)) :
    μ ≫ (moduleFiniteCechFunctor X₀ α₀ U₀ n).map f =
      τ.app (moduleFiniteCechComplex X₀ α₀ U₀ M n) := by
  let : Mono (moduleFiniteCechInclusion X₀ α₀ U₀ M n) := by
    change Mono (HomologicalComplex.ιTruncLE (moduleCechIntComplex X₀ α₀ U₀ M)
      (ComplexShape.embeddingUpIntLE (n : ℤ)))
    infer_instance
  exact tensor_unitor_of_inclusion T τ (moduleFiniteCechInclusion X₀ α₀ U₀ M n)
    (moduleFiniteCechInclusion_naturality X₀ α₀ U₀ f n) hμ ha

/-- Construct the actual chosen-resolution trace comparison inside the finite-model factory. -/
theorem moduleFiniteCechModelComparison_trace [X₀.IsSeparated]
    {M N : X₀.Modules} [hM : M.IsQuasicoherent] [hN : N.IsQuasicoherent]
    (f : M ⟶ N) (n : ℕ) (e : ι₀ ≃ Fin (n + 1))
    (hU : ∀ i, IsAffineOpen (U₀ i)) (hcover : iSup U₀ = ⊤)
    {A S T V : CochainComplex (ModuleCat.{u} R₀) ℤ}
    (μ : A ≅ moduleFiniteCechComplex X₀ α₀ U₀ M n)
    {τ : A ⟶ moduleFiniteCechComplex X₀ α₀ U₀ N n}
    {t : moduleFiniteCechComplex X₀ α₀ U₀ N n ⟶ V}
    {v : A ⟶ S} {w : S ⟶ T} {z : T ⟶ V}
    (old : DerivedCategory.Plus.ι.obj
      ((moduleGlobalSectionsFunctorOfHom X₀ α₀).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj N)) ⟶ DerivedCategory.Q.obj V)
    (hμ : μ.hom ≫ (moduleFiniteCechFunctor X₀ α₀ U₀ n).map f = τ)
    (ht : DerivedCategory.Q.map t =
      (moduleFiniteCechDerivedGlobalSectionsIso X₀ α₀ U₀ N
        (injectiveResolution N) n e hU hcover).hom ≫ old)
    (hv : v ≫ w ≫ z = τ ≫ t) :
    (DerivedCategory.Q.mapIso μ ≪≫ moduleFiniteCechDerivedGlobalSectionsIso
      X₀ α₀ U₀ M (injectiveResolution M) n e hU hcover).inv ≫
        DerivedCategory.Q.map v ≫ DerivedCategory.Q.map w ≫ DerivedCategory.Q.map z =
      DerivedCategory.Plus.ι.map
        ((moduleGlobalSectionsFunctorOfHom X₀ α₀).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).map f)) ≫ old :=
  trace_of_mapped_model DerivedCategory.Q _ rfl
    (moduleFiniteCechCanonicalResolution_naturality X₀ α₀ U₀ f n e hU hcover) hμ ht hv

end FiniteModels

end AlgebraicGeometry.Scheme.Cohomology
