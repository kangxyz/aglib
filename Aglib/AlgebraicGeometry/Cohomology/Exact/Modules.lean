/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.CategoryTheory.Preadditive.Coproducts
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
# Long exact cohomology sequences over a specified structural ring

The original module short exact sequence gives the native additive-sheaf
connecting map. Naturality under multiplication by global functions makes
this same map linear over any specified structural ring. All three adjacent
exactness statements retain the existing coefficient maps on actual `Sheaf.H`.
No quasicoherence, flatness or finiteness premise is required.

The vanishing consequences come last: vanishing of `H^q` is invariant under isomorphism of
coefficients and holds for finite coproducts summandwise
(`moduleCohomology_subsingleton_of_iso`, `moduleCohomology_subsingleton_coproduct`); in a short
exact sequence it passes to the quotient and to the subobject (`moduleCohomology_subsingleton_X₃`,
`moduleCohomology_subsingleton_X₁`), also after tensoring the kernel sequence of an epimorphism
with a finite locally free module (`moduleCohomology_subsingleton_tensor_target`,
`moduleCohomology_subsingleton_tensor_kernel`).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u})

/-- The original module short complex with its scalar action forgotten. -/
abbrev moduleCoefficientSequence (S : ShortComplex X.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  exact S.map F

/-- Actual module short exactness gives actual additive-sheaf short exactness. -/
theorem moduleCoefficientSequence_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) : (moduleCoefficientSequence X S).ShortExact :=
  Scheme.Modules.shortExact_toSheaf hS

/-- Multiplication by a global function is an endomorphism of the original short complex. -/
def moduleCoefficientSequenceScalar (S : ShortComplex X.Modules) (a : Γ(X, ⊤)) :
    moduleCoefficientSequence X S ⟶ moduleCoefficientSequence X S where
  τ₁ := moduleScalarOfGlobal X S.X₁ a
  τ₂ := moduleScalarOfGlobal X S.X₂ a
  τ₃ := moduleScalarOfGlobal X S.X₃ a
  comm₁₂ := moduleScalarOfGlobal_naturality X S.f a
  comm₂₃ := moduleScalarOfGlobal_naturality X S.g a

variable {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))

/-- The native connecting map is linear for the specified structural ring action. -/
def moduleCohomologyConnectingOfHom (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) n →ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) (n + 1) := by
  letI := moduleCohomologyModuleOfHom X α S.X₃ n
  letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
  refine {
    __ := Sheaf.H.δ (moduleCoefficientSequence_shortExact X S hS) n (n + 1) rfl
    map_smul' := fun a x => ?_ }
  exact Sheaf.H.δ_naturality n (n + 1) rfl
    (moduleCoefficientSequence_shortExact X S hS)
    (moduleCoefficientSequence_shortExact X S hS)
    (moduleCoefficientSequenceScalar X S (α a)) x

/-- The linear connecting map retains the literal native additive connecting map. -/
theorem moduleCohomologyConnectingOfHom_apply (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) n) :
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    moduleCohomologyConnectingOfHom X α S hS n x =
      Sheaf.H.δ (moduleCoefficientSequence_shortExact X S hS) n (n + 1) rfl x := rfl

/-- Original coefficient maps form an exact cohomology sequence in every degree. -/
theorem moduleCohomologyMapOfHom_exact (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α S.X₁ n
    letI := moduleCohomologyModuleOfHom X α S.X₂ n
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    Function.Exact (moduleCohomologyMapOfHom X α S.f n)
      (moduleCohomologyMapOfHom X α S.g n) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₂' (moduleCoefficientSequence_shortExact X S hS) n)

/-- Exactness at the term preceding the native connecting map. -/
theorem moduleCohomologyConnectingOfHom_exact_left (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α S.X₂ n
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    Function.Exact (moduleCohomologyMapOfHom X α S.g n)
      (moduleCohomologyConnectingOfHom X α S hS n) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₃' (moduleCoefficientSequence_shortExact X S hS) n (n + 1) rfl)

/-- Exactness at the term following the native connecting map. -/
theorem moduleCohomologyConnectingOfHom_exact_right (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    letI := moduleCohomologyModuleOfHom X α S.X₂ (n + 1)
    Function.Exact (moduleCohomologyConnectingOfHom X α S hS n)
      (moduleCohomologyMapOfHom X α S.f (n + 1)) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₁' (moduleCoefficientSequence_shortExact X S hS) n (n + 1) rfl)

/-- The original connecting maps are natural in an actual morphism of short exact sequences. -/
theorem moduleCohomologyConnectingOfHom_naturality
    {S T : ShortComplex X.Modules} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) n) :
    letI := moduleCohomologyModuleOfHom X α S.X₃ n
    letI := moduleCohomologyModuleOfHom X α S.X₁ (n + 1)
    letI := moduleCohomologyModuleOfHom X α T.X₃ n
    letI := moduleCohomologyModuleOfHom X α T.X₁ (n + 1)
    moduleCohomologyConnectingOfHom X α T hT n
        (moduleCohomologyMapOfHom X α φ.τ₃ n x) =
      moduleCohomologyMapOfHom X α φ.τ₁ (n + 1)
        (moduleCohomologyConnectingOfHom X α S hS n x) := by
  let F : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  exact Sheaf.H.δ_naturality n (n + 1) rfl
    (moduleCoefficientSequence_shortExact X S hS)
    (moduleCoefficientSequence_shortExact X T hT)
    (F.mapShortComplex.map φ) x

/-- An original coefficient monomorphism induces an injective original H⁰ map. -/
theorem moduleH0MapOfHom_injective {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    letI := moduleCohomologyModuleOfHom X α M 0
    letI := moduleCohomologyModuleOfHom X α N 0
    Function.Injective (moduleCohomologyMapOfHom X α f 0) := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let : Mono (F.map f) := inferInstance
  intro x y h
  apply (Ext.addEquiv₀.{u + 1}).injective
  apply (cancel_mono (F.map f)).mp
  change Sheaf.H.map (F.map f) 0 x = Sheaf.H.map (F.map f) 0 y at h
  simpa only [Sheaf.H.addEquiv₀_map] using congrArg (Ext.addEquiv₀.{u + 1}) h

/-! ### Vanishing along short exact sequences -/

section Vanishing

variable {X}

open AlgebraicGeometry.Scheme.Modules

/-- Vanishing of original cohomology is invariant under isomorphism of coefficients. -/
theorem moduleCohomology_subsingleton_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X N) q) := by
  let E := ((moduleCohomologyFunctorOfHom X (RingHom.id Γ(X, ⊤)) q).mapIso e).toLinearEquiv
  exact ⟨fun x y => E.symm.injective (@Subsingleton.elim _ h _ _)⟩

/-- Original cohomology of a finite coproduct, after an additive functor, vanishes when it
vanishes for every summand. -/
theorem moduleCohomology_subsingleton_coproduct (T : X.Modules ⥤ X.Modules) [T.Additive]
    {J : Type u} [Finite J] (f : J → X.Modules) (q : ℕ)
    (h : ∀ j, Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X (T.obj (f j))) q)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X (T.obj (∐ f))) q) := by
  let := Fintype.ofFinite J
  let H := T ⋙ moduleCohomologyFunctorOfHom X (RingHom.id Γ(X, ⊤)) q
  have hb : IsZero (H.obj (∐ f)) :=
    isZero_obj_of_isBilimit H (biconeIsBilimitOfColimitCoconeOfIsColimit
      (colimit.isColimit (Discrete.functor f)))
      (fun j => ModuleCat.isZero_iff_subsingleton.mpr (h j))
  exact ModuleCat.isZero_iff_subsingleton.mp hb

/-- In a short exact sequence, `H^q` of the quotient vanishes when `H^q` of the middle term
and `H^{q+1}` of the subobject vanish. -/
theorem moduleCohomology_subsingleton_X₃ (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (q : ℕ) (h₂ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) q))
    (h₁ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) (q + 1))) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) q) := by
  let α := RingHom.id Γ(X, ⊤)
  let := moduleCohomologyModuleOfHom X α S.X₂ q
  let := moduleCohomologyModuleOfHom X α S.X₃ q
  let := moduleCohomologyModuleOfHom X α S.X₁ (q + 1)
  have hex := moduleCohomologyConnectingOfHom_exact_left X α S hS q
  have hsurj : Function.Surjective (moduleCohomologyMapOfHom X α S.g q) :=
    (LinearMap.surjective_iff_eq_zero_of_exact hex).mpr (Subsingleton.elim _ _)
  exact hsurj.subsingleton

/-- In a short exact sequence, `H^{q+1}` of the subobject vanishes when `H^q` of the quotient
and `H^{q+1}` of the middle term vanish. -/
theorem moduleCohomology_subsingleton_X₁ (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (q : ℕ) (h₃ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) q))
    (h₂ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) (q + 1))) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) (q + 1)) := by
  let α := RingHom.id Γ(X, ⊤)
  let := moduleCohomologyModuleOfHom X α S.X₃ q
  let := moduleCohomologyModuleOfHom X α S.X₁ (q + 1)
  let := moduleCohomologyModuleOfHom X α S.X₂ (q + 1)
  have hex := moduleCohomologyConnectingOfHom_exact_right X α S hS q
  have hz (z : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) (q + 1)) : z = 0 := by
    obtain ⟨w, hw⟩ := (hex z).mp (Subsingleton.elim _ _)
    rw [← hw, Subsingleton.elim w 0, map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Cohomology vanishing along the tensor twist of a kernel sequence of an epimorphism:
`H^q(L ⊗ B)` vanishes when `H^q(L ⊗ A)` and `H^{q+1}(L ⊗ ker π)` do. -/
theorem moduleCohomology_subsingleton_tensor_target (L : X.Modules) [IsFiniteLocallyFree X L]
    {A B : X.Modules} (π : A ⟶ B) [Epi π] (q : ℕ)
    (h₂ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X
      ((moduleTensorLeftFunctor X L).obj A)) q))
    (h₁ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X
      ((moduleTensorLeftFunctor X L).obj (kernel π))) (q + 1))) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X ((moduleTensorLeftFunctor X L).obj B)) q) :=
  moduleCohomology_subsingleton_X₃ _ (tensor_shortExact_finiteLocallyFree L
    (ShortComplex.kernelSequence π)
    { exact := ShortComplex.kernelSequence_exact π, epi_g := inferInstanceAs (Epi π) }) q h₂ h₁

/-- Cohomology vanishing along the tensor twist of a kernel sequence of an epimorphism:
`H^{q+1}(L ⊗ ker π)` vanishes when `H^q(L ⊗ B)` and `H^{q+1}(L ⊗ A)` do. -/
theorem moduleCohomology_subsingleton_tensor_kernel (L : X.Modules) [IsFiniteLocallyFree X L]
    {A B : X.Modules} (π : A ⟶ B) [Epi π] (q : ℕ)
    (h₃ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X
      ((moduleTensorLeftFunctor X L).obj B)) q))
    (h₂ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X
      ((moduleTensorLeftFunctor X L).obj A)) (q + 1))) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X
      ((moduleTensorLeftFunctor X L).obj (kernel π))) (q + 1)) :=
  moduleCohomology_subsingleton_X₁ _ (tensor_shortExact_finiteLocallyFree L
    (ShortComplex.kernelSequence π)
    { exact := ShortComplex.kernelSequence_exact π, epi_g := inferInstanceAs (Epi π) }) q h₃ h₂


end Vanishing

end AlgebraicGeometry.Scheme.Cohomology
