/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Square
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.CartesianSquare
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Open
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections.OpenRestriction

/-! # Scalarization of the complete original cartesian restriction square

Use the four objects and four edges of the accepted additive square together.
The original preimage-open transports remain part of its edges; scalarization
uses their actual module-valued geometric and presheaf maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The tensor square on the four original raw open-cohomology objects. -/
def moduleOpenPullbackTensorSquare
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (M : X.Modules) (U : X.Opens) (n : ℕ) : Square (ModuleCat.{u + 1} S) := by
  -- Detect the tensor square on the original raw maps before native specialization.
  let forgetR := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}
  let forgetS := forget₂ (ModuleCat.{u + 1} S) AddCommGrpCat.{u + 1}
  let build (A C : ModuleCat.{u + 1} R) (B D : ModuleCat.{u + 1} S)
      (q : A ⟶ (ModuleCat.restrictScalars σ).obj B) (l : A ⟶ C)
      (r : B ⟶ D) (δ : C ⟶ (ModuleCat.restrictScalars σ).obj D)
      (q₀ : forgetR.obj A ⟶ forgetS.obj B) (l₀ : forgetR.obj A ⟶ forgetR.obj C)
      (r₀ : forgetS.obj B ⟶ forgetS.obj D) (δ₀ : forgetR.obj C ⟶ forgetS.obj D)
      (h : q₀ ≫ r₀ = l₀ ≫ δ₀)
      (hq₀ : ∀ x, q x = q₀ x) (hl₀ : ∀ x, l x = l₀ x)
      (hr₀ : ∀ x, r x = r₀ x) (hδ₀ : ∀ x, δ x = δ₀ x) :
      Square (ModuleCat.{u + 1} S) := by
    let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ
    let qt := (adj.homEquiv A B).symm q
    let δt := (adj.homEquiv C D).symm δ
    have hqt (x : A) : qt ((1 : S) ⊗ₜ[R,σ] x) = q x :=
      congrArg (fun f => f x) ((adj.homEquiv A B).apply_symm_apply q)
    have hδt (x : C) : δt ((1 : S) ⊗ₜ[R,σ] x) = δ x :=
      congrArg (fun f => f x) ((adj.homEquiv C D).apply_symm_apply δ)
    refine { X₁ := (ModuleCat.extendScalars σ).obj A, X₂ := B
             X₃ := (ModuleCat.extendScalars σ).obj C, X₄ := D
             f₁₂ := qt
             f₁₃ := (ModuleCat.extendScalars σ).map l
             f₂₄ := r, f₃₄ := δt, fac := ?_ }
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change r (qt ((1 : S) ⊗ₜ[R,σ] x)) =
      δt ((ModuleCat.extendScalars σ).map l ((1 : S) ⊗ₜ[R,σ] x))
    rw [hqt, ModuleCat.ExtendScalars.map_tmul, hδt]
    have hx := ConcreteCategory.congr_hom h x
    simp only [ConcreteCategory.comp_apply] at hx
    exact (hr₀ (q x)).trans ((congrArg r₀ (hq₀ x)).trans
      (hx.trans ((congrArg δ₀ (hl₀ x).symm).trans (hδ₀ (l x)).symm)))
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let N : Y.Modules := (Scheme.Modules.pullback p).obj M
  let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
  let ε : N.restrict a ⟶ P :=
    inv ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
  let φp := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let φa := (Scheme.Modules.restrictAdjunction a).unit.app N ≫
    (Scheme.Modules.pushforward a).map ε
  let φj := (Scheme.Modules.restrictAdjunction j).unit.app M
  let φb := (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
  let αU := j.appTop.hom.comp α
  let βV := a.appTop.hom.comp β
  let hs := moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w
  let C := moduleHPrimePresheaf U.toScheme αU (M.restrict j) n
  let D := moduleHPrimePresheaf V.toScheme βV P n
  let κJ : op (j ⁻¹ᵁ U) ⟶ op (⊤ : U.toScheme.Opens) :=
    (eqToHom U.ι_preimage_self.symm).op
  let κA : op (a ⁻¹ᵁ V) ⟶ op (b ⁻¹ᵁ (⊤ : U.toScheme.Opens)) :=
    (eqToHom V.ι_preimage_self.symm).op
  let gp := (moduleHPrimeRestrictionMap p σ α β hσ φp n).app (op U)
  let gj := (moduleHPrimeRestrictionMap j (RingHom.id R) α αU (by rfl) φj n).app (op U)
  let ga := (moduleHPrimeRestrictionMap a (RingHom.id S) β βV (by rfl) φa n).app (op V)
  let gb := (moduleHPrimeRestrictionMap b σ αU βV hs φb n).app (op ⊤)
  let right := ga ≫ (ModuleCat.restrictScalars (RingHom.id S)).map (D.map κA)
  let bottom := C.map κJ ≫ gb
  let A := (moduleHPrimePresheaf X α M n).obj (op U)
  let B := (moduleHPrimePresheaf Y β N n).obj (op V)
  let leftMap : A ⟶ C.obj (op (j ⁻¹ᵁ U)) := gj
  let rightMap : B ⟶ D.obj (op (b ⁻¹ᵁ ⊤)) := right
  let s := moduleOpenPullbackRestrictionSquare p M U n
  have hraw := s.fac
  refine build A (C.obj (op (j ⁻¹ᵁ U))) B (D.obj (op (b ⁻¹ᵁ ⊤)))
    gp leftMap rightMap bottom s.f₁₂ s.f₁₃ s.f₂₄ s.f₃₄ hraw ?_ ?_ ?_ ?_
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl

/-- The upper edge is precisely the original open tensor mate, not merely an
independently chosen map with the same source and target. -/
theorem moduleOpenPullbackTensorSquare_top
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (M : X.Modules) (U : X.Opens) (n : ℕ) :
    (moduleOpenPullbackTensorSquare p σ α β hσ M U n).f₁₂ =
      (moduleHPrimeTensorMap p σ α β hσ
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) n).app (op U) := by
  let N := (Scheme.Modules.pullback p).obj M
  let φp := (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let η := moduleHPrimeRestrictionMap p σ α β hσ φp n
  exact ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).whiskerRight_homEquiv_symm_app
    (moduleHPrimePresheaf X α M n)
    ((Opens.map p.base).op ⋙ moduleHPrimePresheaf Y β N n) η (op U)).symm

/-- The lower raw edge, with its original preimage-open transport and top
comparison, is the literal original global tensor mate. -/
theorem moduleOpenPullbackTensorSquare_bottom_top
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (M : X.Modules) (U : X.Opens) (n : ℕ) :
    let V := p ⁻¹ᵁ U
    let a := V.ι
    let b := p ∣_ U
    let j := U.ι
    let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
    let P := (Scheme.Modules.pullback b).obj (M.restrict j)
    let αU := j.appTop.hom.comp α
    let βV := a.appTop.hom.comp β
    let hs := moduleSectionsOpenSquare_scalars a b p j α β σ hσ h.w
    let φb := (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
    let C := moduleHPrimePresheaf U.toScheme αU (M.restrict j) n
    let κJ := (eqToHom U.ι_preimage_self.symm).op
    letI := moduleHPrimeModuleOfHom U.toScheme αU (M.restrict j) n ⊤
    letI := moduleHPrimeModuleOfHom V.toScheme βV P n ⊤
    letI := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict j) n
    letI := moduleCohomologyModuleOfHom V.toScheme βV P n
    (moduleOpenPullbackTensorSquare p σ α β hσ M U n).f₃₄ ≫
        (moduleHPrimeTopLinearEquivOfHom V.toScheme βV P n).toModuleIso.hom =
      (ModuleCat.extendScalars.{u, u, u + 1} σ).map
        (C.map κJ ≫
          (moduleHPrimeTopLinearEquivOfHom U.toScheme αU (M.restrict j) n).toModuleIso.hom) ≫
          moduleCohomologyTensorMap b σ αU βV hs φb n := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ
  -- Compose the complete mate comparison before substituting native cohomology.
  let finish {A B C : ModuleCat.{u + 1} R} {D E : ModuleCat.{u + 1} S}
      (i : A ⟶ B) (e : B ⟶ C) (q : B ⟶ (ModuleCat.restrictScalars σ).obj D)
      {t : (ModuleCat.extendScalars σ).obj B ⟶ D} (d : D ⟶ E)
      (g : (ModuleCat.extendScalars σ).obj C ⟶ E)
      (hb : t = (adj.homEquiv B D).symm q)
      (ht : t ≫ d = (ModuleCat.extendScalars σ).map e ≫ g) :
      (adj.homEquiv A D).symm (i ≫ q) ≫ d =
        (ModuleCat.extendScalars σ).map (i ≫ e) ≫ g := by
    rw [adj.homEquiv_naturality_left_symm, ← hb, Category.assoc, ht,
      ← Category.assoc, ← Functor.map_comp]
  -- Keep the statement's original let-bound data in the local context.
  intro V a b j h P αU βV hs φb C κJ
  let D := moduleHPrimePresheaf V.toScheme βV P n
  let := moduleHPrimeModuleOfHom U.toScheme αU (M.restrict j) n ⊤
  let := moduleHPrimeModuleOfHom V.toScheme βV P n ⊤
  let := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict j) n
  let := moduleCohomologyModuleOfHom V.toScheme βV P n
  let eC := (moduleHPrimeTopLinearEquivOfHom U.toScheme αU (M.restrict j) n).toModuleIso
  let eD := (moduleHPrimeTopLinearEquivOfHom V.toScheme βV P n).toModuleIso
  let η := moduleHPrimeRestrictionMap b σ αU βV hs φb n
  have hb := adj.whiskerRight_homEquiv_symm_app C ((Opens.map b.base).op ⋙ D) η (op ⊤)
  have ht := moduleHPrimeTensorMap_top b σ αU βV hs φb n
  have hfinal := finish (C.map κJ) eC.hom (η.app (op ⊤)) eD.hom
    (moduleCohomologyTensorMap b σ αU βV hs φb n) hb ht
  exact hfinal

end AlgebraicGeometry.Scheme.Cohomology
