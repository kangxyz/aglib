/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.TwistExt.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.CoefficientsComparison
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Derived.TopHom
public import Mathlib.LinearAlgebra.Contraction

/-!
# Degree-zero projective Serre duality with arbitrary base coefficients

For every native base module J, the unchanged canonical comparison in degree zero
is bijective on coherent modules over a Noetherian ring. Its codomain remains literal
full derived Hom into the degree-n single of J, with the native degree-zero shift.

The proof first uses the actual opposite-twist Ext comparison, original H0 sections,
and the literal global-section tensor map to model negative-twist morphisms with J.
Native coefficient naturality and the original ring-coefficient unitor identify the
canonical map on pure tensors. Original negative-twist duality and the native
finite-free homology tensor/Hom equivalence prove the same comparison bijective
on the actual finite negative-twist sums.

Original resolution/cohomology naturality transfers top-cohomology right exactness
to its small native homology module. Representable Hom into arbitrary J is left
exact there. The same two original finite negative presentations therefore transfer
bijectivity to the original coherent quotient. No flatness, finiteness, projectivity
or injectivity premise is imposed on J, and no flatness or perfectness on M is used.
-/

public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
namespace AlgebraicGeometry.Scheme.Cohomology
universe u

private def coefficientCohomologyZeroSectionsLinearEquiv {R : Type u} [CommRing R]
    (X : Scheme.{u}) (α : R →+* Γ(X, ⊤)) (D : X.Modules) :
    letI := moduleCohomologyModuleOfHom X α D 0
    Sheaf.H.{u + 1} (moduleAddSheaf X D) 0 ≃ₗ[R]
      (moduleSectionsPresheaf X α D).obj (op ⊤) := by
  letI := moduleCohomologyModuleOfHom X α D 0
  letI : Module R (D.val.obj (op ⊤)) := Module.compHom _ α
  exact (moduleH0EquivOfHom X α D).trans (moduleTopSectionsIso X α D).symm.toLinearEquiv

private theorem coefficientCohomologyZeroSectionsLinearEquiv_naturality
    {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
    {D D' : X.Modules} (f : D ⟶ D')
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X D) 0) :
    coefficientCohomologyZeroSectionsLinearEquiv X α D'
      (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map f) 0 x) =
    (((moduleSectionsPresheafFunctor X α).map f).app (op ⊤))
      (coefficientCohomologyZeroSectionsLinearEquiv X α D x) := by
  exact (Sheaf.H.equiv₀_naturality isTerminalTop
    ((SheafOfModules.toSheaf X.ringCatSheaf).map f) x).symm

section TensorCriterion
open scoped TensorProduct
variable {R : Type u} [CommRing R]
variable {A V S T J : Type u}
variable [AddCommGroup A] [Module R A] [AddCommGroup V] [Module R V]
variable [AddCommGroup S] [Module R S] [AddCommGroup T] [Module R T]
variable [AddCommGroup J] [Module R J] [Module.Finite R V] [Module.Free R V]

private theorem tensorCoefficient_bijective_of_generators
    (Q₀ : S ≃ₗ[R] A ⊗[R] R) (Q : T ≃ₗ[R] A ⊗[R] J)
    (f₀ : S →ₗ[R] Module.Dual R V) (f : T →ₗ[R] (V →ₗ[R] J))
    (c : J → S → T)
    (hQ : ∀ j s, Q (c j s) = TensorProduct.map LinearMap.id
      (LinearMap.toSpanSingleton R J j) (Q₀ s))
    (hf : ∀ j s, f (c j s) = (f₀ s).smulRight j)
    (h₀ : Function.Bijective f₀) : Function.Bijective f := by
  let E₀ : S ≃ₗ[R] Module.Dual R V := LinearEquiv.ofBijective f₀ h₀
  let E : A ≃ₗ[R] Module.Dual R V :=
    (TensorProduct.rid R A).symm.trans (Q₀.symm.trans E₀)
  let E' : A ⊗[R] J ≃ₗ[R] (V →ₗ[R] J) :=
    (TensorProduct.congr E (LinearEquiv.refl R J)).trans (dualTensorHomEquiv R V J)
  have h : f.comp Q.symm.toLinearMap = E'.toLinearMap := by
    apply TensorProduct.ext'
    intro a j
    let s := Q₀.symm (a ⊗ₜ[R] (1 : R))
    have hgen : Q (c j s) = a ⊗ₜ[R] j := by
      rw [hQ]
      dsimp only [s]
      rw [Q₀.apply_symm_apply]
      simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.toSpanSingleton_apply, one_smul]
    have hs : Q.symm (a ⊗ₜ[R] j) = c j s :=
      Q.injective ((Q.apply_symm_apply _).trans hgen.symm)
    change f (Q.symm (a ⊗ₜ[R] j)) = E' (a ⊗ₜ[R] j)
    rw [hs, hf]
    apply LinearMap.ext
    intro v
    change f₀ s v • j = E a v • j
    simp only [E, LinearEquiv.trans_apply, TensorProduct.rid_symm_apply,
      E₀, LinearEquiv.ofBijective_apply, s]
  have hformula (x : T) : f x = E' (Q x) := by
    have hx := LinearMap.congr_fun h (Q x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      Q.symm_apply_apply] using hx
  constructor
  · intro x y hxy
    apply Q.injective
    apply E'.injective
    exact (hformula x).symm.trans (hxy.trans (hformula y))
  · intro y
    obtain ⟨z, hz⟩ := E'.surjective y
    refine ⟨Q.symm z, ?_⟩
    exact (LinearMap.congr_fun h z).trans hz

end TensorCriterion

variable (R : Type u) [CommRing R] (ι : Type u) [Fintype ι]

private def twistHomTensorCoefficientsLinearEquiv
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (a b : ℤ) (hd : -(n : ℤ) ≤ -a + b)
    (J : ModuleCat.{u} R) :
    let X : Scheme.{u} := ProjectiveSpace R ι
    let α : R →+* Γ(X, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let N : X.Modules := twistingSheafTensorCoefficients R ι b J
    letI := moduleCategoryLinearOfHom X α
    (twistingSheaf R ι a ⟶ N) ≃ₗ[R]
      (tensorRight J).obj
        ((moduleSectionsPresheaf X α (twistingSheaf R ι (-a + b))).obj (op ⊤)) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCategoryLinearOfHom X α
  let D : X.Modules := twistingSheafTensorCoefficients R ι (-a + b) J
  letI := moduleCohomologyModuleOfHom X α D 0
  exact (Ext.linearEquiv₀ (R := R) (C := X.Modules)).symm.trans
    ((twistingTensorCoefficientsExtCohomologyLinearEquiv R ι a b J 0).trans
      ((coefficientCohomologyZeroSectionsLinearEquiv X α D).trans
        (twistingTensorTildeSectionsIso R ι n e (-a + b) hd J).symm.toLinearEquiv))

private theorem twistHomTensorCoefficientsLinearEquiv_apply
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (a b : ℤ) (hd : -(n : ℤ) ≤ -a + b)
    (J : ModuleCat.{u} R)
    (f : twistingSheaf R ι a ⟶ twistingSheafTensorCoefficients R ι b J) :
    (twistingTensorTildeSectionsIso R ι n e (-a + b) hd J).hom
      (twistHomTensorCoefficientsLinearEquiv R ι n e a b hd J f) =
    coefficientCohomologyZeroSectionsLinearEquiv (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
      (twistingSheafTensorCoefficients R ι (-a + b) J)
      (twistingTensorCoefficientsExtCohomologyAddEquiv R ι a b J 0 (Ext.mk₀ f)) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let Φ := coefficientCohomologyZeroSectionsLinearEquiv X α
    (twistingSheafTensorCoefficients R ι (-a + b) J)
  have h := congrArg (fun E => Φ (E (Ext.mk₀ f)))
    (twistingTensorCoefficientsExtCohomologyLinearEquiv_toAddEquiv R ι a b J 0)
  let B := twistingTensorTildeSectionsIso R ι n e (-a + b) hd J
  exact (B.toLinearEquiv.apply_symm_apply _).trans h

private theorem twistHomTensorCoefficientsLinearEquiv_naturality
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (a b : ℤ) (hd : -(n : ℤ) ≤ -a + b)
    {J J' : ModuleCat.{u} R} (f : J ⟶ J')
    (g : twistingSheaf R ι a ⟶ twistingSheafTensorCoefficients R ι b J) :
    twistHomTensorCoefficientsLinearEquiv R ι n e a b hd J'
      (g ≫ (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι b)).map
        ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))) =
    (((tensoringRight (ModuleCat.{u} R)).map f).app
      ((moduleSectionsPresheaf (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (twistingSheaf R ι (-a + b))).obj (op ⊤)))
      (twistHomTensorCoefficientsLinearEquiv R ι n e a b hd J g) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let δ := (moduleTensorLeftFunctor X (twistingSheaf R ι (-a + b))).map
    ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))
  let B := twistingTensorTildeSectionsIso R ι n e (-a + b) hd J
  let B' := twistingTensorTildeSectionsIso R ι n e (-a + b) hd J'
  apply B'.toLinearEquiv.injective
  change B'.hom _ = B'.hom _
  rw [twistHomTensorCoefficientsLinearEquiv_apply]
  have hE := twistingTensorCoefficientsExtCohomologyAddEquiv_naturality_coefficients
    R ι a b f 0 (Ext.mk₀ g)
  rw [Ext.mk₀_comp_mk₀] at hE
  rw [hE, coefficientCohomologyZeroSectionsLinearEquiv_naturality]
  have hB := congrArg (fun η => η.app (op ⊤))
    (moduleTensorTildeSectionsMap_naturality_coefficients (toSpec R ι)
      (twistingSheaf R ι (-a + b)) f)
  have hBx := congrArg
    (fun t => t (twistHomTensorCoefficientsLinearEquiv R ι n e a b hd J g)) hB
  change (((moduleSectionsPresheafFunctor X α).map δ).app (op ⊤))
      (B.hom (twistHomTensorCoefficientsLinearEquiv R ι n e a b hd J g)) =
    B'.hom _ at hBx
  rw [twistHomTensorCoefficientsLinearEquiv_apply] at hBx
  exact hBx

/-- The standard derived-category model for modules on `ProjectiveSpace R ι`, used locally. -/
local instance coefficientTopSource :
    HasDerivedCategory.{u + 1} (ProjectiveSpace R ι).Modules :=
  HasDerivedCategory.standard _
/-- The standard derived-category model for `R`-modules, used locally. -/
local instance coefficientTopTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private def coefficientShiftZeroHomLinearEquiv
    (K V : DerivedCategory (ModuleCat.{u} R)) :
    (K ⟶ V⟦(0 : ℤ)⟧) ≃ₗ[R] (K ⟶ V) where
  __ := (ShiftedHom.homEquiv (X := K) (Y := V) (0 : ℤ) rfl).symm
  map_add' f g := by
    change (f + g) ≫ _ = f ≫ _ + g ≫ _
    rw [Preadditive.add_comp]
  map_smul' r f := by
    change (r • f) ≫ _ = r • (f ≫ _)
    rw [Linear.smul_comp]

private def coefficientTopHomLinearEquiv (K : DerivedCategory (ModuleCat.{u} R))
    (n : ℤ) [K.IsLE n] (J : ModuleCat.{u} R) :
    (K ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj J) ≃ₗ[R]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K ⟶ J) where
  __ := DerivedCategory.homToSingleAddEquiv K n J
  map_smul' r f := by
    change DerivedCategory.homToSingleAddEquiv K n J (r • f) =
      r • DerivedCategory.homToSingleAddEquiv K n J f
    have hf : r • f = f ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).map
        (r • 𝟙 J) := by
      rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
        Linear.comp_smul, Category.comp_id]
    rw [hf]
    exact (DerivedCategory.homToSingleAddEquiv_naturality_right K n f (r • 𝟙 J)).trans
      (by rw [Linear.comp_smul, Category.comp_id])

private def coefficientDerivedTopHomologyLinearEquiv
    (K : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) [K.IsLE n]
    (J : ModuleCat.{u} R) :
    (K ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj J)⟦(0 : ℤ)⟧) ≃ₗ[R]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K ⟶ J) :=
  (coefficientShiftZeroHomLinearEquiv R K _).trans
    (coefficientTopHomLinearEquiv R K n J)

private def coefficientTopSerreMap
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent] :
    let X : Scheme.{u} := ProjectiveSpace R ι
    let α : R →+* Γ(X, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let K := ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
    letI := moduleCategoryLinearOfHom X α
    (M ⟶ projectiveResidueTwistTensorCoefficients R ι J) →ₗ[R]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj K ⟶ J) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let K := ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  letI := moduleCategoryLinearOfHom X α
  letI := projectiveDerivedGlobalSectionsSingle_isLE R ι n e M
  exact (coefficientDerivedTopHomologyLinearEquiv R K (n : ℤ) J).toLinearMap.comp
    ((projectiveDerivedSerreMapCoefficients R ι n e J M 0).comp
      (Ext.linearEquiv₀ (R := R) (C := X.Modules)).symm.toLinearMap)

private theorem coefficientTopSerreMap_apply
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent]
    (f : M ⟶ projectiveResidueTwistTensorCoefficients R ι J)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj M))) :
    coefficientTopSerreMap R ι n e J M f x =
      projectiveTraceCoefficientsLinearEquiv R ι n e J
        (moduleCohomologyMapOfHom (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) f n
          (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
            ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
            (injectiveResolution M) n x)) :=
  projectiveDerivedSerreMapCoefficients_mk₀_homology_apply R ι n e J M
    (injectiveResolution M) f x

private theorem coefficientDerivedTopHomologyLinearEquiv_naturality_right
    (K : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) [K.IsLE n]
    {J J' : ModuleCat.{u} R}
    (φ : K ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj J)⟦(0 : ℤ)⟧)
    (f : J ⟶ J') :
    coefficientDerivedTopHomologyLinearEquiv R K n J'
      (φ ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (0 : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).map f)) =
      coefficientDerivedTopHomologyLinearEquiv R K n J φ ≫ f := by
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj J
  let V' := (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj J'
  let g := (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).map f
  let z := shiftFunctorZero' (DerivedCategory (ModuleCat.{u} R)) (0 : ℤ) rfl
  have hz := z.hom.naturality g
  change (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (0 : ℤ)).map g ≫
    z.hom.app V' = z.hom.app V ≫ g at hz
  change DerivedCategory.homToSingleAddEquiv K n J'
      ((φ ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (0 : ℤ)).map g) ≫
        z.hom.app V') =
    DerivedCategory.homToSingleAddEquiv K n J (φ ≫ z.hom.app V) ≫ f
  rw [Category.assoc, hz, ← Category.assoc]
  exact DerivedCategory.homToSingleAddEquiv_naturality_right K n _ f

private theorem coefficientDerivedTopHomologyLinearEquiv_naturality_left
    {K L : DerivedCategory (ModuleCat.{u} R)} (n : ℤ) [K.IsLE n] [L.IsLE n]
    (J : ModuleCat.{u} R) (f : K ⟶ L)
    (φ : L ⟶ ((DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj J)⟦(0 : ℤ)⟧) :
    coefficientDerivedTopHomologyLinearEquiv R K n J (f ≫ φ) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map f ≫
        coefficientDerivedTopHomologyLinearEquiv R L n J φ := by
  change DerivedCategory.homToSingleAddEquiv K n J ((f ≫ φ) ≫ _) =
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map f ≫
      DerivedCategory.homToSingleAddEquiv L n J (φ ≫ _)
  rw [Category.assoc]
  exact DerivedCategory.homToSingleAddEquiv_naturality_left n J f _

private theorem coefficientTopSerreMap_naturality_coefficients
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {J J' : ModuleCat.{u} R} (f : J ⟶ J')
    (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent]
    (g : M ⟶ projectiveResidueTwistTensorCoefficients R ι J) :
    coefficientTopSerreMap R ι n e J' M
      (g ≫ (moduleTensorLeftFunctor (ProjectiveSpace R ι)
        (twistingSheaf R ι (-(Fintype.card ι : ℤ)))).map
          ((Scheme.Modules.pullback (toSpec R ι)).map (tilde.map f))) =
      coefficientTopSerreMap R ι n e J M g ≫ f := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let K := ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let := projectiveDerivedGlobalSectionsSingle_isLE R ι n e M
  change coefficientDerivedTopHomologyLinearEquiv R K (n : ℤ) J'
    (projectiveDerivedSerreMapCoefficients R ι n e J' M 0 (Ext.mk₀ (g ≫ _))) =
    coefficientDerivedTopHomologyLinearEquiv R K (n : ℤ) J
      (projectiveDerivedSerreMapCoefficients R ι n e J M 0 (Ext.mk₀ g)) ≫ f
  rw [← Ext.mk₀_comp_mk₀, projectiveDerivedSerreMapCoefficients_naturality_coefficients]
  exact coefficientDerivedTopHomologyLinearEquiv_naturality_right R K (n : ℤ) _ f

private theorem coefficientTopSerreMap_self_apply
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent]
    (f : M ⟶ projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).obj
      (((moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0).obj M))) :
    coefficientTopSerreMap R ι n e (ModuleCat.of R R) M f x =
      projectiveTopSerreMap R ι n e M (f ≫ (projectiveResidueTwistTensorSelfIso R ι).hom)
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (injectiveResolution M) n x) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let K := ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let := projectiveDerivedGlobalSectionsSingle_isLE R ι n e M
  change (coefficientDerivedTopHomologyLinearEquiv R K (n : ℤ) (ModuleCat.of R R)
    (projectiveDerivedSerreMapCoefficients R ι n e (ModuleCat.of R R) M 0 (Ext.mk₀ f))) x = _
  rw [projectiveDerivedSerreMapCoefficients_self, Ext.mk₀_comp_mk₀]
  exact projectiveDerivedSerreMap_mk₀_homology_apply R ι n e M (injectiveResolution M)
    (f ≫ (projectiveResidueTwistTensorSelfIso R ι).hom) x

private abbrev coefficientTopCohomologyFunctor (n : ℕ) :
    (ProjectiveSpace R ι).Modules ⥤ ModuleCat.{u} R :=
  DerivedCategory.Plus.singleFunctor (ProjectiveSpace R ι).Modules 0 ⋙
    (moduleGlobalSectionsFunctorOfHom (ProjectiveSpace R ι)
      ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)

omit [Fintype ι] in
private theorem coefficientTopCohomologyFunctor_naturality (n : ℕ)
    {M N : (ProjectiveSpace R ι).Modules} (f : M ⟶ N)
    (x : (coefficientTopCohomologyFunctor R ι n).obj M) :
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
        (injectiveResolution N) n ((coefficientTopCohomologyFunctor R ι n).map f x) =
      moduleCohomologyMapOfHom (ProjectiveSpace R ι)
        ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) f n
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv (ProjectiveSpace R ι)
          ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)
          (injectiveResolution M) n x) := by
  let I := injectiveResolution M
  let I' := injectiveResolution N
  let φ : InjectiveResolution.Hom I I' f :=
    ⟨InjectiveResolution.desc f I' I, by
      simpa only [CochainComplex.single₀_map_f_zero] using
        InjectiveResolution.desc_commutes_zero f I' I⟩
  exact moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_naturality
    (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) φ n x

omit [Fintype ι] in
private theorem coefficientTopCohomologyFunctor_map_epi
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M N : (ProjectiveSpace R ι).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] : Epi ((coefficientTopCohomologyFunctor R ι n).map f) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α (injectiveResolution M) n
  let E' := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α (injectiveResolution N) n
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro z
  obtain ⟨x, hx⟩ := (projectiveTopCohomologyMap_surjective_of_epi R ι n e f) (E' z)
  refine ⟨E.symm x, ?_⟩
  apply E'.injective
  rw [coefficientTopCohomologyFunctor_naturality, E.apply_symm_apply]
  exact hx

omit [Fintype ι] in
private theorem coefficientTopCohomologyFunctor_exact
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace R ι).Modules) (hS : S.Exact) [Epi S.g]
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (coefficientTopCohomologyFunctor R ι n)).Exact := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let E₁ := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
    (injectiveResolution S.X₁) n
  let E₂ := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
    (injectiveResolution S.X₂) n
  let E₃ := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
    (injectiveResolution S.X₃) n
  have h := projectiveTopCohomology_exact R ι n e S hS
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro y hy
  have hy' : moduleCohomologyMapOfHom X α S.g n (E₂ y) = 0 := by
    have h0 := congrArg E₃ hy
    have hN := coefficientTopCohomologyFunctor_naturality R ι n S.g y
    exact hN.symm.trans (h0.trans E₃.map_zero)
  have hfun : ∀ z : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) n,
      moduleCohomologyMapOfHom X α S.g n z = 0 →
        ∃ x : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) n,
          moduleCohomologyMapOfHom X α S.f n x = z :=
    (ShortComplex.moduleCat_exact_iff _).mp h
  obtain ⟨x, hx⟩ := hfun (E₂ y) hy'
  refine ⟨E₁.symm x, ?_⟩
  apply E₂.injective
  exact (coefficientTopCohomologyFunctor_naturality R ι n S.f (E₁.symm x)).trans
    ((congrArg (moduleCohomologyMapOfHom X α S.f n) (E₁.apply_symm_apply x)).trans hx)

private theorem coefficientTopSerreMap_naturality
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    {M N : (ProjectiveSpace R ι).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) (g : N ⟶ projectiveResidueTwistTensorCoefficients R ι J) :
    coefficientTopSerreMap R ι n e J M (f ≫ g) =
      (coefficientTopCohomologyFunctor R ι n).map f ≫
        coefficientTopSerreMap R ι n e J N g := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let K := F.obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let L := F.obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj N)
  let := projectiveDerivedGlobalSectionsSingle_isLE R ι n e M
  let := projectiveDerivedGlobalSectionsSingle_isLE R ι n e N
  change coefficientDerivedTopHomologyLinearEquiv R K (n : ℤ) J
      (projectiveDerivedSerreMapCoefficients R ι n e J M 0 (Ext.mk₀ (f ≫ g))) =
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (F.map ((DerivedCategory.Plus.singleFunctor X.Modules 0).map f)) ≫
        coefficientDerivedTopHomologyLinearEquiv R L (n : ℤ) J
          (projectiveDerivedSerreMapCoefficients R ι n e J N 0 (Ext.mk₀ g))
  rw [← Ext.mk₀_comp_mk₀, projectiveDerivedSerreMapCoefficients_naturality]
  exact coefficientDerivedTopHomologyLinearEquiv_naturality_left R (n : ℤ) J _ _

private theorem coefficientTopSerreMap_self_bijective
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace R ι).Modules) [M.IsQuasicoherent]
    (h : Function.Bijective (projectiveTopSerreMap R ι n e M)) :
    Function.Bijective (coefficientTopSerreMap R ι n e (ModuleCat.of R R) M) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom X α
  let := moduleCohomologyModuleOfHom X α M n
  let ω := twistingSheaf R ι (-(Fintype.card ι : ℤ))
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α (injectiveResolution M) n
  let U : (M ⟶ projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R)) ≃
      (M ⟶ ω) := {
    toFun := fun f => f ≫ (projectiveResidueTwistTensorSelfIso R ι).hom
    invFun := fun f => f ≫ (projectiveResidueTwistTensorSelfIso R ι).inv
    left_inv := by intro f; simp
    right_inv := by intro f; simp }
  let W : ((coefficientTopCohomologyFunctor R ι n).obj M ⟶ ModuleCat.of R R) ≃
      (Sheaf.H.{u + 1} (moduleAddSheaf X M) n →ₗ[R] R) :=
    ModuleCat.homEquiv.trans (LinearEquiv.arrowCongr E (LinearEquiv.refl R R)).toEquiv
  have hW (f : M ⟶ projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R)) :
      W (coefficientTopSerreMap R ι n e (ModuleCat.of R R) M f) =
        projectiveTopSerreMap R ι n e M (U f) := by
    ext z
    exact (coefficientTopSerreMap_self_apply R ι n e M f (E.symm z)).trans
      (congrArg (projectiveTopSerreMap R ι n e M (U f)) (E.apply_symm_apply z))
  constructor
  · intro f g hfg
    apply U.injective
    apply h.injective
    exact (hW f).symm.trans ((congrArg W hfg).trans (hW g))
  · intro z
    obtain ⟨f, hf⟩ := h.surjective (W z)
    refine ⟨U.symm f, W.injective ?_⟩
    exact (hW (U.symm f)).trans
      ((congrArg (projectiveTopSerreMap R ι n e M) (U.apply_symm_apply f)).trans hf)

private theorem coefficientTopSerreMap_negativeTwist_bijective
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : ℕ) (hN : Fintype.card ι ≤ N)
    (J : ModuleCat.{u} R) :
    Function.Bijective (coefficientTopSerreMap R ι n e J (twistingSheaf R ι (-(N : ℤ)))) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom X α
  let a : ℤ := -(N : ℤ)
  let b : ℤ := -(Fintype.card ι : ℤ)
  let M : X.Modules := twistingSheaf R ι a
  let V := (coefficientTopCohomologyFunctor R ι n).obj M
  let := moduleCohomologyModuleOfHom X α M n
  let E := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α (injectiveResolution M) n
  let := twistingCohomology_free R ι n e a n
  let := twistingCohomology_finite R ι n e a n
  let : Module.Free R V := Module.Free.of_equiv E.symm
  let : Module.Finite R V := Module.Finite.equiv E.symm
  have hd : -(n : ℤ) ≤ -a + b := by
    have hN' : (Fintype.card ι : ℤ) ≤ N := by exact_mod_cast hN
    dsimp only [a, b]
    omega
  let Q₀ := twistHomTensorCoefficientsLinearEquiv R ι n e a b hd (ModuleCat.of R R)
  let Q := twistHomTensorCoefficientsLinearEquiv R ι n e a b hd J
  let e₀ : (V ⟶ ModuleCat.of R R) ≃ₗ[R] Module.Dual R V := ModuleCat.homLinearEquiv
  let eJ : (V ⟶ J) ≃ₗ[R] (V →ₗ[R] J) := ModuleCat.homLinearEquiv
  let f₀ := e₀.toLinearMap.comp (coefficientTopSerreMap R ι n e (ModuleCat.of R R) M)
  let f := eJ.toLinearMap.comp (coefficientTopSerreMap R ι n e J M)
  let c (j : J) (s : M ⟶ projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R)) :=
    s ≫ (moduleTensorLeftFunctor X (twistingSheaf R ι b)).map
      ((Scheme.Modules.pullback (toSpec R ι)).map
        (tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R J j))))
  have hQ (j : J)
      (s : M ⟶ projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R)) :
      Q (c j s) = TensorProduct.map LinearMap.id (LinearMap.toSpanSingleton R J j) (Q₀ s) :=
    twistHomTensorCoefficientsLinearEquiv_naturality R ι n e a b hd
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R J j)) s
  have hf (j : J)
      (s : M ⟶ projectiveResidueTwistTensorCoefficients R ι (ModuleCat.of R R)) :
      f (c j s) = (f₀ s).smulRight j := by
    exact congrArg ModuleCat.Hom.hom
      (coefficientTopSerreMap_naturality_coefficients R ι n e
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R J j)) M s)
  have h₀ : Function.Bijective (coefficientTopSerreMap R ι n e (ModuleCat.of R R) M) := by
    apply coefficientTopSerreMap_self_bijective R ι n e M
    have hdeg : a = -((N - Fintype.card ι : ℕ) : ℤ) - (Fintype.card ι : ℤ) := by
      dsimp only [a]
      omega
    change Function.Bijective (projectiveTopSerreMap R ι n e (twistingSheaf R ι a))
    rw [hdeg]
    exact projectiveTopSerreMap_residueTwist_bijective R ι n e (N - Fintype.card ι)
  have hbij : Function.Bijective f :=
    tensorCoefficient_bijective_of_generators Q₀ Q f₀ f c hQ hf (e₀.bijective.comp h₀)
  constructor
  · intro x y hxy
    exact hbij.injective (congrArg ModuleCat.Hom.hom hxy)
  · intro y
    obtain ⟨x, hx⟩ := hbij.surjective y.hom
    exact ⟨x, ModuleCat.hom_ext hx⟩

private theorem coefficientTopSerreMap_twistingCoproduct_bijective
    {I : Type u} [Finite I] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (J : ModuleCat.{u} R) (d : I → ℤ)
    (h : ∀ a, Function.Bijective (coefficientTopSerreMap R ι n e J (twistingSheaf R ι (d a)))) :
    letI := twistingCoproduct_isQuasicoherent R ι d
    Function.Bijective (coefficientTopSerreMap R ι n e J
      (∐ fun a => twistingSheaf R ι (d a))) := by
  classical
  let := twistingCoproduct_isQuasicoherent R ι d
  let F : I → (ProjectiveSpace R ι).Modules := fun a => twistingSheaf R ι (d a)
  let H := coefficientTopCohomologyFunctor R ι n
  constructor
  · intro f g hfg
    apply Sigma.hom_ext
    intro a
    apply (h a).injective
    rw [coefficientTopSerreMap_naturality, coefficientTopSerreMap_naturality]
    exact congrArg (fun φ => H.map (Sigma.ι F a) ≫ φ) hfg
  · intro φ
    choose f hf using fun a => (h a).surjective (H.map (Sigma.ι F a) ≫ φ)
    refine ⟨Sigma.desc f, ?_⟩
    apply (cancel_epi (sigmaComparison H F)).mp
    apply Sigma.hom_ext
    intro a
    rw [ι_comp_sigmaComparison_assoc, ι_comp_sigmaComparison_assoc,
      ← coefficientTopSerreMap_naturality, Sigma.ι_comp_desc]
    exact hf a

private theorem coefficientTopSerreMap_uniformNegativeCoproduct_bijective
    {I : Type u} [Finite I] (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : ℕ)
    (hN : Fintype.card ι ≤ N) (J : ModuleCat.{u} R) :
    letI := twistingCoproduct_isQuasicoherent R ι (fun _ : I => -(N : ℤ))
    Function.Bijective (coefficientTopSerreMap R ι n e J
      (∐ fun _ : I => twistingSheaf R ι (-(N : ℤ)))) :=
  coefficientTopSerreMap_twistingCoproduct_bijective R ι n e J (fun _ : I => -(N : ℤ))
    (fun _ => coefficientTopSerreMap_negativeTwist_bijective R ι n e N hN J)

private theorem coefficientTopSerreMap_bijective_of_presentation
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (S : ShortComplex (ProjectiveSpace R ι).Modules) (hS : S.Exact) [Epi S.g]
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h₂ : Function.Bijective (coefficientTopSerreMap R ι n e J S.X₂))
    (h₁ : Function.Bijective (coefficientTopSerreMap R ι n e J S.X₁)) :
    Function.Bijective (coefficientTopSerreMap R ι n e J S.X₃) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let ω := projectiveResidueTwistTensorCoefficients R ι J
  let H := coefficientTopCohomologyFunctor R ι n
  let F : X.Modulesᵒᵖ ⥤ AddCommGrpCat.{u} := preadditiveYoneda.obj ω
  let G : (ModuleCat.{u} R)ᵒᵖ ⥤ AddCommGrpCat.{u} := preadditiveYoneda.obj J
  let A := S.op.map F
  let B := (S.map H).op.map G
  let : Mono S.op.f := inferInstanceAs (Mono S.g.op)
  have hA : A.Exact := hS.op.map_of_mono_of_preservesKernel F inferInstance inferInstance
  let : Mono A.f := inferInstanceAs (Mono (F.map S.g.op))
  have hH : (S.map H).Exact := coefficientTopCohomologyFunctor_exact R ι n e S hS
  let : Epi (H.map S.g) := coefficientTopCohomologyFunctor_map_epi R ι n e S.g
  let : Mono (S.map H).op.f := inferInstanceAs (Mono (H.map S.g).op)
  have hB : B.Exact := hH.op.map_of_mono_of_preservesKernel G inferInstance inferInstance
  let : Mono B.f := inferInstanceAs (Mono (G.map (H.map S.g).op))
  let τ (M : X.Modules) [M.IsQuasicoherent] :
      AddCommGrpCat.of (M ⟶ ω) ⟶ AddCommGrpCat.of (H.obj M ⟶ J) :=
    AddCommGrpCat.ofHom (coefficientTopSerreMap R ι n e J M).toAddMonoidHom
  let φ : A ⟶ B := {
    τ₁ := τ S.X₃
    τ₂ := τ S.X₂
    τ₃ := τ S.X₁
    comm₁₂ := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change H.map S.g ≫ coefficientTopSerreMap R ι n e J S.X₃ f =
        coefficientTopSerreMap R ι n e J S.X₂ (S.g ≫ f)
      exact (coefficientTopSerreMap_naturality R ι n e J S.g f).symm
    comm₂₃ := by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro f
      change H.map S.f ≫ coefficientTopSerreMap R ι n e J S.X₂ f =
        coefficientTopSerreMap R ι n e J S.X₁ (S.f ≫ f)
      exact (coefficientTopSerreMap_naturality R ι n e J S.f f).symm }
  have hmid : IsIso φ.τ₂ := (ConcreteCategory.isIso_iff_bijective _).mpr h₂
  let : IsIso φ.τ₃ := (ConcreteCategory.isIso_iff_bijective _).mpr h₁
  have hleft : IsIso φ.τ₁ :=
    CategoryTheory.Abelian.isIso_of_isIso_of_mono (ShortComplex.mapToComposableArrows φ)
      hA.exact_toComposableArrows hB.exact_toComposableArrows
      (inferInstanceAs (Mono A.f)) (inferInstanceAs (Mono B.f)) hmid
      (inferInstanceAs (Mono φ.τ₃))
  exact (ConcreteCategory.isIso_iff_bijective _).mp hleft

@[expose] public section

/-- For every native base module, the original degree-zero comparison is bijective
on every coherent module over a Noetherian base ring. -/
theorem projectiveDerivedSerreMapCoefficients_zero_bijective [IsNoetherianRing R]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (J : ModuleCat.{u} R)
    (M : (ProjectiveSpace R ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M) :
    Function.Bijective (projectiveDerivedSerreMapCoefficients R ι n e J M 0) := by
  let X : Scheme.{u} := ProjectiveSpace R ι
  let α : R →+* Γ(X, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCategoryLinearOfHom X α
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  obtain ⟨N, hN, L, hL, I, hI, QIndex, hQIndex, d, π, hd, hS, hπ⟩ :=
    exists_uniformNegativeTwistTwoStepPresentation R ι M hM (Fintype.card ι)
  let := hI
  let := hQIndex
  let S := ShortComplex.mk d π hd
  let : Epi S.g := hπ
  let : S.X₁.IsQuasicoherent :=
    twistingCoproduct_isQuasicoherent R ι (fun _ : QIndex => -(L : ℤ))
  let : S.X₂.IsQuasicoherent :=
    twistingCoproduct_isQuasicoherent R ι (fun _ : I => -(N : ℤ))
  have htop : Function.Bijective (coefficientTopSerreMap R ι n e J M) :=
    coefficientTopSerreMap_bijective_of_presentation R ι n e J S hS
      (coefficientTopSerreMap_uniformNegativeCoproduct_bijective (I := I) R ι n e N hN J)
      (coefficientTopSerreMap_uniformNegativeCoproduct_bijective (I := QIndex)
        R ι n e L hL J)
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι
  let K := F.obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)
  let := projectiveDerivedGlobalSectionsSingle_isLE R ι n e M
  let E := coefficientDerivedTopHomologyLinearEquiv R K (n : ℤ) J
  let ω := projectiveResidueTwistTensorCoefficients R ι J
  constructor
  · intro x y hxy
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective M ω).surjective x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective M ω).surjective y
    apply congrArg Ext.mk₀
    apply htop.injective
    exact congrArg E hxy
  · intro z
    obtain ⟨f, hf⟩ := htop.surjective (E z)
    exact ⟨Ext.mk₀ f, E.injective hf⟩

end

end AlgebraicGeometry.Scheme.Cohomology
