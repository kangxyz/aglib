/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Composition
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Functor

/-!
# Coefficient naturality of the original module cohomology scalar mates

Every actual commuting square of module coefficient arrows gives the same
commuting square for the original scalar-adjunction mates. Global cohomology
uses the existing module-valued functor on the unchanged native groups.
A compatible triangle of the original geometric arrows transports epimorphy
and invertibility through an isomorphism of structural rings. No flatness
or finiteness condition is imposed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
  (p : Y ⟶ X) (σ : R →+* S)
  (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
  (hp : p.appTop.hom.comp α = β.comp σ)
  {M M' : X.Modules} {N N' : Y.Modules}
  (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
  (φ' : M' ⟶ (Scheme.Modules.pushforward p).obj N')
  (μ : M ⟶ M') (ν : N ⟶ N')
  (h : μ ≫ φ' = φ ≫ (Scheme.Modules.pushforward p).map ν) (n : ℕ)

include h in
/-- An actual coefficient square gives the corresponding square of original
semilinear maps with the specified structural scalars. -/
theorem moduleCohomologyRestrictionMap_naturality :
    (moduleCohomologyFunctorOfHom X α n).map μ ≫
        moduleCohomologyRestrictionMap p σ α β hp φ' n =
      moduleCohomologyRestrictionMap p σ α β hp φ n ≫
        (ModuleCat.restrictScalars σ).map ((moduleCohomologyFunctorOfHom Y β n).map ν) := by
  ext x
  exact moduleCohomologyMapAlong_naturality p φ φ' μ ν h n x

set_option maxHeartbeats 800000 in
-- The coefficient square retains the original four structural cohomology actions.
/-- An actual coefficient square gives the corresponding square of the original
tensor mates, retaining both original coefficient maps. -/
theorem moduleCohomologyTensorMap_naturality
    (h : μ ≫ φ' = φ ≫ (Scheme.Modules.pushforward p).map ν) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u + 1} σ).map ((moduleCohomologyFunctorOfHom X α n).map μ) ≫
        moduleCohomologyTensorMap p σ α β hp φ' n =
      moduleCohomologyTensorMap p σ α β hp φ n ≫
        (moduleCohomologyFunctorOfHom Y β n).map ν := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom X α M' n
  let := moduleCohomologyModuleOfHom Y β N n
  let := moduleCohomologyModuleOfHom Y β N' n
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change moduleCohomologyTensorMap p σ α β hp φ' n
      ((ModuleCat.extendScalars.{u, u, u + 1} σ).map ((moduleCohomologyFunctorOfHom X α n).map μ)
        ((1 : S) ⊗ₜ[R,σ] x)) =
    (moduleCohomologyFunctorOfHom Y β n).map ν
      (moduleCohomologyTensorMap p σ α β hp φ n ((1 : S) ⊗ₜ[R,σ] x))
  erw [ModuleCat.ExtendScalars.map_tmul, moduleCohomologyTensorMap_one_tmul,
    moduleCohomologyTensorMap_one_tmul]
  exact moduleCohomologyMapAlong_naturality p φ φ' μ ν h n x

/-- For a scheme isomorphism, an actual invertible coefficient arrow and an
isomorphism of structural rings, the original tensor mate is invertible. -/
theorem moduleCohomologyTensorMap_isIso_of_ringEquiv
    (p : Y ⟶ X) [IsIso p] (e : R ≃+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (h : p.appTop.hom.comp α = β.comp e.toRingHom)
    {M : X.Modules} {N : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) [IsIso φ] (n : ℕ) :
    IsIso (moduleCohomologyTensorMap p e.toRingHom α β h φ n) := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β N n
  let μ := moduleCohomologyRestrictionMap p e.toRingHom α β h φ n
  let : IsIso μ := (ConcreteCategory.isIso_iff_bijective μ).mpr
    (moduleCohomologyMapAlong_bijective p φ n)
  have ht : IsIso ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} e.toRingHom).unit.app
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n)) ≫
      (ModuleCat.restrictScalars e.toRingHom).map
        (moduleCohomologyTensorMap p e.toRingHom α β h φ n)) := by
    rw [moduleCohomologyTensorMap_unit]
    exact inferInstanceAs (IsIso μ)
  let : IsIso ((ModuleCat.restrictScalars e.toRingHom).map
      (moduleCohomologyTensorMap p e.toRingHom α β h φ n)) :=
    IsIso.of_isIso_comp_left
      ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} e.toRingHom).unit.app
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n)))
      ((ModuleCat.restrictScalars e.toRingHom).map
        (moduleCohomologyTensorMap p e.toRingHom α β h φ n))
  exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars e.toRingHom)

/-- A unit-tensor triangle gives the native scalar-composition identity. -/
private theorem scalarTensorMap_comp_eq
    {T : Type u} [CommRing T] (σ : R →+* S) (e : S ≃+* T)
    {A : ModuleCat.{u + 1} R} {B : ModuleCat.{u + 1} S} {C : ModuleCat.{u + 1} T}
    (a : (ModuleCat.extendScalars.{u, u, u + 1} σ).obj A ⟶ B)
    (b : (ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom).obj B ⟶ C)
    (c : (ModuleCat.extendScalars.{u, u, u + 1} (e.toRingHom.comp σ)).obj A ⟶ C)
    (h : ∀ x : A, b ((1 : T) ⊗ₜ[S,e.toRingHom] a ((1 : S) ⊗ₜ[R,σ] x)) =
      c ((1 : T) ⊗ₜ[R,e.toRingHom.comp σ] x)) :
    (ModuleCat.extendScalarsComp.{u, u + 1} σ e.toRingHom).hom.app A ≫
        (ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom).map a ≫ b = c := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change b ((ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom).map a
    ((ModuleCat.extendScalarsComp.{u, u + 1} σ e.toRingHom).hom.app A
      ((1 : T) ⊗ₜ[R,e.toRingHom.comp σ] x))) = c ((1 : T) ⊗ₜ[R,e.toRingHom.comp σ] x)
  rw [ModuleCat.extendScalarsComp_hom_app_one_tmul, ModuleCat.ExtendScalars.map_tmul]
  exact h x

/-- Unit-tensor compatibility transports epimorphy across native scalar extension
and an invertible target comparison. -/
private theorem scalarTensorMap_epi_iff_ringEquiv
    {T : Type u} [CommRing T] (σ : R →+* S) (e : S ≃+* T)
    {A : ModuleCat.{u + 1} R} {B : ModuleCat.{u + 1} S} {C : ModuleCat.{u + 1} T}
    (a : (ModuleCat.extendScalars.{u, u, u + 1} σ).obj A ⟶ B)
    (b : (ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom).obj B ⟶ C) [IsIso b]
    (c : (ModuleCat.extendScalars.{u, u, u + 1} (e.toRingHom.comp σ)).obj A ⟶ C)
    (h : ∀ x : A, b ((1 : T) ⊗ₜ[S,e.toRingHom] a ((1 : S) ⊗ₜ[R,σ] x)) =
      c ((1 : T) ⊗ₜ[R,e.toRingHom.comp σ] x)) : Epi c ↔ Epi a := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} e.toRingHom
  let : (ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  rw [← scalarTensorMap_comp_eq σ e a b c h, epi_comp_iff_of_epi,
    epi_comp_iff_of_isIso]
  exact Functor.epi_map_iff_epi (ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom) a
    (hF₁ := Functor.preservesEpimorphisms_of_adjunction adj)
    (hF₂ := Functor.reflectsEpimorphisms_of_faithful
      (ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom))

/-- The same native unit-tensor triangle transports invertibility across an
isomorphism of target rings. -/
private theorem scalarTensorMap_isIso_iff_ringEquiv
    {T : Type u} [CommRing T] (σ : R →+* S) (e : S ≃+* T)
    {A : ModuleCat.{u + 1} R} {B : ModuleCat.{u + 1} S} {C : ModuleCat.{u + 1} T}
    (a : (ModuleCat.extendScalars.{u, u, u + 1} σ).obj A ⟶ B)
    (b : (ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom).obj B ⟶ C) [IsIso b]
    (c : (ModuleCat.extendScalars.{u, u, u + 1} (e.toRingHom.comp σ)).obj A ⟶ C)
    (h : ∀ x : A, b ((1 : T) ⊗ₜ[S,e.toRingHom] a ((1 : S) ⊗ₜ[R,σ] x)) =
      c ((1 : T) ⊗ₜ[R,e.toRingHom.comp σ] x)) : IsIso c ↔ IsIso a := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} e.toRingHom
  let : (ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  rw [← scalarTensorMap_comp_eq σ e a b c h, isIso_comp_left_iff, isIso_comp_right_iff]
  exact isIso_iff_of_reflects_iso a (ModuleCat.extendScalars.{u, u, u + 1} e.toRingHom)

set_option maxHeartbeats 800000 in
-- The original scalar mates retain all three displayed structural cohomology actions.
/-- A commuting triangle of the actual geometric cohomology arrows transports
epimorphy of their original tensor mates across an isomorphism of target rings.
Both the scheme arrow and the coefficient arrow in the transport are invertible. -/
theorem moduleCohomologyTensorMap_epi_iff_of_ringEquiv_triangle
    {Z : Scheme.{u}} {T : Type u} [CommRing T]
    (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X) [IsIso q]
    (σ : R →+* S) (e : S ≃+* T)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤)) (γ : T →+* Γ(Z, ⊤))
    (hp : p.appTop.hom.comp α = β.comp σ)
    (hq : q.appTop.hom.comp β = γ.comp e.toRingHom)
    (hr : r.appTop.hom.comp α = γ.comp (e.toRingHom.comp σ))
    {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (ψ : N ⟶ (Scheme.Modules.pushforward q).obj P) [IsIso ψ]
    (ρ : M ⟶ (Scheme.Modules.pushforward r).obj P) (n : ℕ)
    (h : ∀ x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n,
      moduleCohomologyMapAlong q ψ n (moduleCohomologyMapAlong p φ n x) =
        moduleCohomologyMapAlong r ρ n x) :
    Epi (moduleCohomologyTensorMap r (e.toRingHom.comp σ) α γ hr ρ n) ↔
      Epi (moduleCohomologyTensorMap p σ α β hp φ n) := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β N n
  let := moduleCohomologyModuleOfHom Z γ P n
  let : IsIso (moduleCohomologyTensorMap q e.toRingHom β γ hq ψ n) :=
    moduleCohomologyTensorMap_isIso_of_ringEquiv q e β γ hq ψ n
  apply scalarTensorMap_epi_iff_ringEquiv σ e
    (moduleCohomologyTensorMap p σ α β hp φ n)
    (moduleCohomologyTensorMap q e.toRingHom β γ hq ψ n)
    (moduleCohomologyTensorMap r (e.toRingHom.comp σ) α γ hr ρ n)
  intro x
  erw [moduleCohomologyTensorMap_one_tmul, moduleCohomologyTensorMap_one_tmul,
    moduleCohomologyTensorMap_one_tmul]
  exact h x

set_option maxHeartbeats 800000 in
-- The original scalar mates retain all three displayed structural cohomology actions.
/-- A commuting triangle of the actual geometric cohomology arrows transports
invertibility of their original tensor mates across an isomorphism of target rings.
Both the scheme arrow and the coefficient arrow in the transport are invertible. -/
theorem moduleCohomologyTensorMap_isIso_iff_of_ringEquiv_triangle
    {Z : Scheme.{u}} {T : Type u} [CommRing T]
    (p : Y ⟶ X) (q : Z ⟶ Y) (r : Z ⟶ X) [IsIso q]
    (σ : R →+* S) (e : S ≃+* T)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤)) (γ : T →+* Γ(Z, ⊤))
    (hp : p.appTop.hom.comp α = β.comp σ)
    (hq : q.appTop.hom.comp β = γ.comp e.toRingHom)
    (hr : r.appTop.hom.comp α = γ.comp (e.toRingHom.comp σ))
    {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (ψ : N ⟶ (Scheme.Modules.pushforward q).obj P) [IsIso ψ]
    (ρ : M ⟶ (Scheme.Modules.pushforward r).obj P) (n : ℕ)
    (h : ∀ x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n,
      moduleCohomologyMapAlong q ψ n (moduleCohomologyMapAlong p φ n x) =
        moduleCohomologyMapAlong r ρ n x) :
    IsIso (moduleCohomologyTensorMap r (e.toRingHom.comp σ) α γ hr ρ n) ↔
      IsIso (moduleCohomologyTensorMap p σ α β hp φ n) := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β N n
  let := moduleCohomologyModuleOfHom Z γ P n
  let : IsIso (moduleCohomologyTensorMap q e.toRingHom β γ hq ψ n) :=
    moduleCohomologyTensorMap_isIso_of_ringEquiv q e β γ hq ψ n
  apply scalarTensorMap_isIso_iff_ringEquiv σ e
    (moduleCohomologyTensorMap p σ α β hp φ n)
    (moduleCohomologyTensorMap q e.toRingHom β γ hq ψ n)
    (moduleCohomologyTensorMap r (e.toRingHom.comp σ) α γ hr ρ n)
  intro x
  erw [moduleCohomologyTensorMap_one_tmul, moduleCohomologyTensorMap_one_tmul,
    moduleCohomologyTensorMap_one_tmul]
  exact h x


end AlgebraicGeometry.Scheme.Cohomology
