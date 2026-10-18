/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Open
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Open

/-!
# Composition of the original module cohomology scalar mates

The original global and open cohomology maps compose through the native
extension and restriction of scalars comparisons. The coefficient arrow is
the original composite through module direct image. No flatness or finiteness
condition is imposed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y Z : Scheme.{u}} {R S T : Type u}
  [CommRing R] [CommRing S] [CommRing T]
  (p : Y ⟶ X) (q : Z ⟶ Y) (σ : R →+* S) (τ : S →+* T)
  (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤)) (γ : T →+* Γ(Z, ⊤))
  (hp : p.appTop.hom.comp α = β.comp σ)
  (hq : q.appTop.hom.comp β = γ.comp τ)
  (hqp : (q ≫ p).appTop.hom.comp α = γ.comp (τ.comp σ))
  {M : X.Modules} {N : Y.Modules} {P : Z.Modules}
  (φ : M ⟶ (Scheme.Modules.pushforward p).obj N)
  (ψ : N ⟶ (Scheme.Modules.pushforward q).obj P) (n : ℕ)

/-- Successive original semilinear cohomology maps compose through the native
restriction-of-scalars comparison and the actual composite coefficient arrow. -/
theorem moduleCohomologyRestrictionMap_comp :
    let := moduleCohomologyModuleOfHom X α M n
    let := moduleCohomologyModuleOfHom Y β N n
    let := moduleCohomologyModuleOfHom Z γ P n
    moduleCohomologyRestrictionMap p σ α β hp φ n ≫
        (ModuleCat.restrictScalars σ).map
          (moduleCohomologyRestrictionMap q τ β γ hq ψ n) =
      moduleCohomologyRestrictionMap (q ≫ p) (τ.comp σ) α γ hqp
          (φ ≫ (Scheme.Modules.pushforward p).map ψ ≫
            (Scheme.Modules.pushforwardComp q p).hom.app P) n ≫
        (ModuleCat.restrictScalarsComp.{u + 1} σ τ).hom.app
          (ModuleCat.of T (Sheaf.H.{u + 1} (moduleAddSheaf Z P) n)) := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β N n
  let := moduleCohomologyModuleOfHom Z γ P n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact moduleCohomologyMapAlong_comp p q φ ψ n x

/-- Unit pure tensors detect composition through the native extension-of-scalars comparison. -/
private theorem scalarTensorMap_comp
    (σ : R →+* S) (τ : S →+* T)
    {A : ModuleCat.{u + 1} R} {B : ModuleCat.{u + 1} S} {C : ModuleCat.{u + 1} T}
    (a : (ModuleCat.extendScalars σ).obj A ⟶ B)
    (b : (ModuleCat.extendScalars τ).obj B ⟶ C)
    (c : (ModuleCat.extendScalars (τ.comp σ)).obj A ⟶ C)
    (h : ∀ x : A, b ((1 : T) ⊗ₜ[S,τ] a ((1 : S) ⊗ₜ[R,σ] x)) =
      c ((1 : T) ⊗ₜ[R,τ.comp σ] x)) :
    (ModuleCat.extendScalarsComp.{u, u + 1} σ τ).hom.app A ≫
        (ModuleCat.extendScalars τ).map a ≫ b = c := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change b ((ModuleCat.extendScalars τ).map a
    ((ModuleCat.extendScalarsComp.{u, u + 1} σ τ).hom.app A
      ((1 : T) ⊗ₜ[R,τ.comp σ] x))) = c ((1 : T) ⊗ₜ[R,τ.comp σ] x)
  rw [ModuleCat.extendScalarsComp_hom_app_one_tmul, ModuleCat.ExtendScalars.map_tmul]
  exact h x

set_option maxHeartbeats 800000 in
-- The native composition comparison elaborates through three original cohomology actions.
/-- The original tensor mates compose through the native extension-of-scalars
comparison, with the same actual geometric and coefficient maps. -/
theorem moduleCohomologyTensorMap_comp :
    let := moduleCohomologyModuleOfHom X α M n
    let := moduleCohomologyModuleOfHom Y β N n
    let := moduleCohomologyModuleOfHom Z γ P n
    let A : ModuleCat.{u + 1} R := .of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n)
    let B : ModuleCat.{u + 1} S := .of S (Sheaf.H.{u + 1} (moduleAddSheaf Y N) n)
    let C : ModuleCat.{u + 1} T := .of T (Sheaf.H.{u + 1} (moduleAddSheaf Z P) n)
    let a : (ModuleCat.extendScalars σ).obj A ⟶ B :=
      moduleCohomologyTensorMap p σ α β hp φ n
    let b : (ModuleCat.extendScalars τ).obj B ⟶ C :=
      moduleCohomologyTensorMap q τ β γ hq ψ n
    let c : (ModuleCat.extendScalars (τ.comp σ)).obj A ⟶ C :=
      moduleCohomologyTensorMap (q ≫ p) (τ.comp σ) α γ hqp
        (φ ≫ (Scheme.Modules.pushforward p).map ψ ≫
          (Scheme.Modules.pushforwardComp q p).hom.app P) n
    (ModuleCat.extendScalarsComp.{u, u + 1} σ τ).hom.app A ≫
        (ModuleCat.extendScalars τ).map a ≫ b = c := by
  apply scalarTensorMap_comp
  intro x
  erw [moduleCohomologyTensorMap_one_tmul, moduleCohomologyTensorMap_one_tmul,
    moduleCohomologyTensorMap_one_tmul]
  exact moduleCohomologyMapAlong_comp p q φ ψ n x

/-- Successive original module pullbacks on cohomology agree with the original
pullback along the composite, through the native module pullback comparison. -/
theorem moduleCohomologyPullback_comp (p : Y ⟶ X) (q : Z ⟶ Y)
    (M : X.Modules) (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf Z.ringCatSheaf).map
        ((Scheme.Modules.pullbackComp q p).hom.app M)) n
      (moduleCohomologyPullback q ((Scheme.Modules.pullback p).obj M) n
        (moduleCohomologyPullback p M n x)) =
      moduleCohomologyPullback (q ≫ p) M n x := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction p
  let B := Scheme.Modules.pullbackPushforwardAdjunction q
  let C := Scheme.Modules.pullbackPushforwardAdjunction (q ≫ p)
  let e := (Scheme.Modules.pullbackComp q p).app M
  have hu := unit_conjugateEquiv (A.comp B) C
    (Scheme.Modules.pullbackComp q p).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at hu
  have hv := congrArg (fun k => k ≫ (Scheme.Modules.pushforward (q ≫ p)).map e.hom) hu
  have he : (Scheme.Modules.pullbackComp q p).inv.app M ≫ e.hom = 𝟙 _ :=
    (Scheme.Modules.pullbackComp q p).inv_hom_id_app M
  simp only [Category.assoc, ← Functor.map_comp, he] at hv
  have hn := (Scheme.Modules.pushforwardComp q p).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  have hc : A.unit.app M ≫
        (Scheme.Modules.pushforward p).map
          (B.unit.app ((Scheme.Modules.pullback p).obj M) ≫
            (Scheme.Modules.pushforward q).map e.hom) ≫
          (Scheme.Modules.pushforwardComp q p).hom.app _ = C.unit.app M := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hn]
    exact hv
  change Sheaf.H.map ((SheafOfModules.toSheaf Z.ringCatSheaf).map e.hom) n
      (moduleCohomologyMapAlong q (B.unit.app _) n
        (moduleCohomologyMapAlong p (A.unit.app M) n x)) =
    moduleCohomologyMapAlong (q ≫ p) (C.unit.app M) n x
  erw [← moduleCohomologyMapAlong_postcomp, moduleCohomologyMapAlong_comp, hc]

/-- Equal geometric morphisms give the same original module pullback on cohomology
under the actual native pullback equality comparison. -/
theorem moduleCohomologyPullback_congr (p q : Y ⟶ X) (h : p = q)
    (M : X.Modules) (n : ℕ) (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map
        ((Scheme.Modules.pullbackCongr h).hom.app M)) n
      (moduleCohomologyPullback p M n x) = moduleCohomologyPullback q M n x := by
  subst q
  simp [Scheme.Modules.pullbackCongr]

end AlgebraicGeometry.Scheme.Cohomology
