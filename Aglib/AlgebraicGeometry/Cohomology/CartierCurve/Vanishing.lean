/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistCohomology
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyAffine
public import Aglib.AlgebraicGeometry.Modules.Generators.GlobalSections

/-!
# Cohomology and sections along a projective-line quotient filtration

The quotient maps and short complexes are actual module-sheaf maps on the
original scheme. An isomorphism identifies each quotient with the direct image
of a native projective-line twist. The sharp twist theorem proves quotient
vanishing; exactness then propagates first-cohomology vanishing and lifts every
original quotient section. No vanishing or section-lifting assumption is made
for a successor term.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology.CartierCurve

universe u

variable {X : Scheme.{u}}

/-- First cohomology of the middle term vanishes when both adjacent terms do. -/
theorem h1_subsingleton_middle (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) 1))
    (h₃ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) 1)) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) 1) := by
  let α := RingHom.id Γ(X, ⊤)
  let := moduleCohomologyModuleOfHom X α S.X₁ 1
  let := moduleCohomologyModuleOfHom X α S.X₂ 1
  let := moduleCohomologyModuleOfHom X α S.X₃ 1
  have hex := moduleCohomologyMapOfHom_exact X α S hS 1
  have hz (z : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₂) 1) : z = 0 := by
    obtain ⟨w, hw⟩ := (hex z).mp (@Subsingleton.elim _ h₃ _ _)
    rw [← hw, @Subsingleton.elim _ h₁ w 0, map_zero]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Vanishing of first cohomology of the kernel lifts every original quotient section. -/
theorem sections_surjective_of_h1_subsingleton (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (h₁ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) 1)) :
    Function.Surjective (S.g.val.app (op ⊤)) := by
  apply surjective_of_moduleCohomologyConnectingOfHom_zero_eq_zero
    (RingHom.id Γ(X, ⊤)) S hS
  let := moduleCohomologyModuleOfHom X (RingHom.id Γ(X, ⊤)) S.X₃ 0
  let := moduleCohomologyModuleOfHom X (RingHom.id Γ(X, ⊤)) S.X₁ (0 + 1)
  exact LinearMap.ext (fun _ => @Subsingleton.elim _ h₁ _ _)

/-- An actual finite generating-section object gives its original finite family
of morphisms from the structure module. -/
theorem finite_family_of_generatingSections {M : X.Modules}
    (σ : SheafOfModules.GeneratingSections M) (hσ : σ.IsFiniteType) :
    ∃ (J : Type u) (_ : Finite J) (s : J → (𝟙_ X.Modules ⟶ M)), Epi (Sigma.desc s) := by
  rcases hσ with ⟨hI⟩
  let : Finite σ.I := hI
  let s (j : σ.I) : 𝟙_ X.Modules ⟶ M :=
    Sigma.ι (fun _ : σ.I => 𝟙_ X.Modules) j ≫ σ.π
  refine ⟨σ.I, inferInstance, s, ?_⟩
  have heq : Sigma.desc s = σ.π := by
    apply Sigma.hom_ext
    intro j
    simp only [s, Sigma.ι_comp_desc]
  rw [heq]
  exact σ.epi

/-- Transport finite global generators along the given actual module isomorphism. -/
theorem finite_family_of_iso {M N : X.Modules} (e : M ≅ N)
    {J : Type u} (s : J → (𝟙_ X.Modules ⟶ M))
    (hs : Epi (Sigma.desc s)) :
    ∃ t : J → (𝟙_ X.Modules ⟶ N), Epi (Sigma.desc t) := by
  let : Epi (Sigma.desc s) := hs
  refine ⟨fun j => s j ≫ e.hom, ?_⟩
  have heq : (Sigma.desc fun j => s j ≫ e.hom) = Sigma.desc s ≫ e.hom := by
    apply Sigma.hom_ext
    intro j
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
  rw [heq]
  infer_instance

/-- Lift finite quotient generators through the original section map and combine
them with actual kernel generators. Exactness proves that the combined family
is epimorphic; no local frame or Nakayama premise is assumed. -/
theorem finite_family_middle (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {J K : Type u}
    (sA : J → (𝟙_ X.Modules ⟶ S.X₁)) (hA : Epi (Sigma.desc sA))
    (sC : K → (𝟙_ X.Modules ⟶ S.X₃)) (hC : Epi (Sigma.desc sC))
    (hg : Function.Surjective (S.g.val.app (op ⊤))) :
    ∃ s : J ⊕ K → (𝟙_ X.Modules ⟶ S.X₂), Epi (Sigma.desc s) := by
  classical
  let : Epi (Sigma.desc sA) := hA
  let : Epi (Sigma.desc sC) := hC
  choose t ht using fun k => exists_unitHom_factor_of_surjective S.g hg (sC k)
  let s : J ⊕ K → (𝟙_ X.Modules ⟶ S.X₂) := Sum.elim (fun j => sA j ≫ S.f) t
  let π := Sigma.desc s
  refine ⟨s, ⟨?_⟩⟩
  intro Z f g h
  let δ := f - g
  have hδ : π ≫ δ = 0 := by
    dsimp only [π, δ]
    rw [Preadditive.comp_sub, h, sub_self]
  have hAδ : S.f ≫ δ = 0 := by
    apply (cancel_epi (Sigma.desc sA)).mp
    apply Sigma.hom_ext
    intro j
    simpa only [π, s, Sum.elim_inl, Sigma.ι_comp_desc_assoc, Category.assoc, comp_zero] using
      congrArg (fun q => Sigma.ι (fun _ : J ⊕ K => 𝟙_ X.Modules) (Sum.inl j) ≫ q) hδ
  let q := hS.gIsCokernel.desc (CokernelCofork.ofπ δ hAδ)
  have hfac : S.g ≫ q = δ := hS.gIsCokernel.fac _ WalkingParallelPair.one
  have htδ (k : K) : t k ≫ δ = 0 := by
    simpa only [π, s, Sum.elim_inr, Sigma.ι_comp_desc_assoc, comp_zero] using
      congrArg (fun q => Sigma.ι (fun _ : J ⊕ K => 𝟙_ X.Modules) (Sum.inr k) ≫ q) hδ
  have hq : q = 0 := by
    apply (cancel_epi (Sigma.desc sC)).mp
    apply Sigma.hom_ext
    intro k
    simp only [Sigma.ι_comp_desc_assoc, comp_zero]
    rw [← ht k, Category.assoc, hfac, htδ]
  have hz : δ = 0 := by rw [← hfac, hq, comp_zero]
  exact sub_eq_zero.mp hz

/-- Any prescribed additional finite section family can be retained verbatim
without losing generation by an existing finite family. -/
theorem augment_finite_family {M : X.Modules} {J K : Type u}
    (s : J → (𝟙_ X.Modules ⟶ M)) (hs : Epi (Sigma.desc s))
    (t : K → (𝟙_ X.Modules ⟶ M)) :
    ∃ v : J ⊕ K → (𝟙_ X.Modules ⟶ M), Epi (Sigma.desc v) ∧ ∀ k, v (Sum.inr k) = t k := by
  let : Epi (Sigma.desc s) := hs
  refine ⟨Sum.elim s t, ?_, fun _ => rfl⟩
  constructor
  intro Z f g h
  apply (cancel_epi (Sigma.desc s)).mp
  apply Sigma.hom_ext
  intro j
  simpa only [Sigma.ι_comp_desc_assoc, Sum.elim_inl] using
    congrArg (fun q => Sigma.ι (fun _ : J ⊕ K => 𝟙_ X.Modules) (Sum.inl j) ≫ q) h

variable [CompactSpace X] [X.IsSeparated]
  {k : Type u} [CommRing k]
  (i : ProjectiveSpace k (ULift.{u} (Fin 2)) ⟶ X) [IsAffineHom i]

/-- Direct images of native projective-line twists have zero positive cohomology
for every degree at least minus one. No field or Noetherian premise is needed. -/
theorem pushforward_twist_cohomology_subsingleton (d : ℤ) (hd : -1 ≤ d)
    (q : ℕ) (hq : q ≠ 0) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X
      ((Scheme.Modules.pushforward i).obj
        (twistingSheaf k (ULift.{u} (Fin 2)) d))) q) := by
  let := twistingCohomology_subsingleton_of_neg_le_degree
    k (ULift.{u} (Fin 2)) 1 Equiv.ulift d q hd hq
  exact (moduleCohomologyAffinePushforward_bijective i
    (twistingSheaf k (ULift.{u} (Fin 2)) d) q).injective.subsingleton

/-- The actual finite filtration inherits first-cohomology vanishing from its
initial term and lifts every quotient section. The quotient comparisons are
module-sheaf isomorphisms; no quotient vanishing is assumed. -/
theorem filtration_vanishing_and_section_lifts
    (M Q : ℕ → X.Modules)
    (a : ∀ j, M j ⟶ M (j + 1)) (b : ∀ j, M (j + 1) ⟶ Q j)
    (w : ∀ j, a j ≫ b j = 0)
    (d : ℤ) (N : ℕ) (hN : (N : ℤ) ≤ d + 1)
    (hS : ∀ j, j < N → (ShortComplex.mk (a j) (b j) (w j)).ShortExact)
    (eQ : ∀ j, j < N → (Q j ≅ (Scheme.Modules.pushforward i).obj
      (twistingSheaf k (ULift.{u} (Fin 2)) (d - (j : ℤ) - 1))))
    (h₀ : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X (M 0)) 1)) :
    (∀ j, j ≤ N → Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X (M j)) 1)) ∧
    (∀ j, j < N → Function.Surjective ((b j).val.app (op ⊤))) := by
  have hvan : ∀ j, j ≤ N →
      Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X (M j)) 1) := by
    intro j
    induction j with
    | zero => exact fun _ => h₀
    | succ j ih =>
      intro hj
      have hjN : j < N := by omega
      have hquot : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X (Q j)) 1) :=
        moduleCohomology_subsingleton_of_iso (eQ j hjN).symm 1
          (pushforward_twist_cohomology_subsingleton i (d - (j : ℤ) - 1)
            (by omega) 1 (by decide))
      exact h1_subsingleton_middle (ShortComplex.mk (a j) (b j) (w j))
        (hS j hjN) (ih (by omega)) hquot
  refine ⟨hvan, fun j hj => ?_⟩
  exact sections_surjective_of_h1_subsingleton (ShortComplex.mk (a j) (b j) (w j))
    (hS j hj) (hvan j (by omega))

end AlgebraicGeometry.Scheme.Cohomology.CartierCurve
