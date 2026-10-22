/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Boundary.InitialFamily
public import Aglib.AlgebraicGeometry.Compactification.Boundary.Assembly
public import Aglib.AlgebraicGeometry.Compactification.Boundary.ModifiedPatch

/-!
# The actual finite patch family for Noetherian compactification

The original dense affine cover supplies all proper models. Boundary
modification gives an actual proper finite-product image covered by opens
mapping into separated patches containing the original source. No assumed
compactification or quasi-domination provider occurs in the theorem.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- Concrete finite patches with a common original dense open and an actual
proper source covered by the domains of the patch maps. -/
theorem exists_finite_patch_family
    {X S : Scheme.{u}} [IsNoetherian S]
    (p : X ⟶ S) [IsSeparated p] [QuasiCompact p] [LocallyOfFiniteType p] [Nonempty X] :
    ∃ (U : X.Opens) (P : Scheme.{u}) (pP : P ⟶ S) (c : U.toScheme ⟶ P)
      (n : ℕ) (O : Fin (n + 1) → P.Opens) (M : Fin (n + 1) → Scheme.{u})
      (pM : ∀ a, M a ⟶ S) (x : ∀ a, X ⟶ M a)
      (k : ∀ a, (O a).toScheme ⟶ M a) (a : ∀ b, U.toScheme ⟶ (O b).toScheme),
      Dense (U : Set X) ∧ IsNoetherian P ∧ IsProper pP ∧
      IsOpenImmersion c ∧ IsSchemeTheoreticallyDominant c ∧ c ≫ pP = U.ι ≫ p ∧
      (⨆ b, O b) = ⊤ ∧
      (∀ b, IsNoetherian (M b) ∧ IsSeparated (pM b) ∧ QuasiCompact (pM b) ∧
        LocallyOfFiniteType (pM b) ∧ IsOpenImmersion (x b) ∧
        IsSchemeTheoreticallyDominant (x b) ∧ x b ≫ pM b = p ∧
        k b ≫ pM b = (O b).ι ≫ pP ∧ a b ≫ (O b).ι = c ∧
        a b ≫ k b = U.ι ≫ x b) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨E⟩ := exists_initialPatchFamily p
  let A : Over S := Over.mk (E.U.ι ≫ p)
  let : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian E.U.ι
  let : NoetherianSpace A.left := by
    change NoetherianSpace (E.U : Set X)
    infer_instance
  let : IsNoetherian A.left := ⟨⟩
  let : ∀ b, IsProper (E.C b).hom := E.proper
  let : ∀ b, IsProper (E.q b) := E.properQ
  let : ∀ b, IsIso (E.q b ∣_ E.W b) := E.isoQ
  let : ∀ b, IsOpenImmersion (E.s b) := E.openS
  let : ∀ b, IsSchemeTheoreticallyDominant (E.s b) := E.dominantS
  let : ∀ b, IsSchemeTheoreticallyDominant (E.V b).ι := E.dominantV
  let inc : ∀ b, E.U.toScheme ⟶ (E.W b).toScheme := fun b => X.homOfLE (E.le b)
  let av : ∀ b, A.left ⟶ (E.V b).toScheme := fun b => inc b ≫ E.s b
  have hav : ∀ b, av b ≫ E.q b = E.U.ι := by
    intro b
    dsimp only [av, inc]
    rw [Category.assoc, E.source, Scheme.homOfLE_ι]
  let j : ∀ b, A ⟶ E.C b := fun b => Over.homMk (av b ≫ (E.V b).ι) (by
    rw [Category.assoc, E.over, ← Category.assoc, hav]
    rfl)
  let : IsOpenImmersion (j 0).left := by
    change IsOpenImmersion ((inc 0 ≫ E.s 0) ≫ (E.V 0).ι)
    dsimp only [inc]
    infer_instance
  obtain ⟨C', β, j', hβ, hpC', hj', himm, hempty⟩ :=
    exists_finite_boundary_modification E.C j p E.V E.denseV E.q E.over av
      (fun _ => rfl) E.U.ι hav E.W E.cover
  let : ∀ b, IsProper (C' b).hom := hpC'
  let : ∀ b, IsIso ((β b).left ∣_ E.V b) := fun b => (hβ b).restrict_isIso
  let : IsImmersion (j' 0).left := himm
  choose OY M pM x o r hOY hM hsep hqc hlft hx hxd ho hr hrd hxp hop hxr hrY using
    fun b => exists_modified_boundary_patch p (E.C b).hom (E.V b) (E.q b)
      (E.over b) (E.W b) (E.s b) (E.source b) (β b).left (hβ b)
  have hjlift : ∀ b, (j' b).left =
      inc b ≫ E.s b ≫ inv ((β b).left ∣_ E.V b) ≫ ((β b).left ⁻¹ᵁ E.V b).ι := by
    intro b
    apply (β b).left.ext_of_isIso_restriction (E.V b) (av b)
    · exact congrArg (fun z => z.left) (hj' b)
    · simp only [av, Category.assoc, ← morphismRestrict_ι,
        IsIso.inv_hom_id_assoc]
  have hrj : ∀ b, (inc b ≫ r b) ≫ (OY b).ι = (j' b).left := by
    intro b
    rw [Category.assoc, hrY b, hjlift b]
  let f := (finiteProductOverLift C' j').left
  let P := f.image
  let c : E.U.toScheme ⟶ P := f.toImage
  let pP : P ⟶ S := f.imageι ≫ (finiteProductOver C').hom
  let π : ∀ b, P ⟶ (C' b).left := fun b => f.imageι ≫ (finiteProductOverπ C' b).left
  let : IsProper (finiteProductOver C').hom := isProper_finiteProductOver C'
  let : IsProper pP := inferInstance
  let : IsNoetherian P := finiteProductOverLift_image_isNoetherian C' j'
  obtain ⟨hc, hdc⟩ := finiteProductOverLift_toImage_properties C' j' 0
  have hcp : c ≫ pP = E.U.ι ≫ p := by
    dsimp only [c, pP]
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact (finiteProductOverLift C' j').w
  have hcπ : ∀ b, c ≫ π b = (j' b).left := by
    intro b
    dsimp only [c, π]
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact congrArg (fun z => z.left) (finiteProductOverLift_π C' j' b)
  have hπp : ∀ b, π b ≫ (C' b).hom = pP := by
    intro b
    dsimp only [π, pP]
    rw [Category.assoc, finiteProductOverπ_hom]
  let O : Fin (E.n + 1) → P.Opens := fun b => π b ⁻¹ᵁ OY b
  let k : ∀ b, (O b).toScheme ⟶ M b := fun b => (π b ∣_ OY b) ≫ o b
  have hlift : ∀ b, (inc b ≫ r b) ≫ (OY b).ι = c ≫ π b := by
    intro b
    rw [hrj b, hcπ b]
  let a : ∀ b, E.U.toScheme ⟶ (O b).toScheme := fun b =>
    (isPullback_morphismRestrict (π b) (OY b)).lift (inc b ≫ r b) c (hlift b)
  have haO : ∀ b, a b ≫ (O b).ι = c := fun b =>
    (isPullback_morphismRestrict (π b) (OY b)).lift_snd _ _ _
  have har : ∀ b, a b ≫ (π b ∣_ OY b) = inc b ≫ r b := fun b =>
    (isPullback_morphismRestrict (π b) (OY b)).lift_fst _ _ _
  have hcover : (⨆ b, O b) = ⊤ := by
    apply top_unique
    intro z _
    have hex : ∃ b, z ∉ (π b) ⁻¹'
        closure ((β b).left ⁻¹' ((E.V b).ι '' (E.q b ⁻¹' (E.W b : Set X)ᶜ))) := by
      by_contra hn
      push Not at hn
      have hz := Set.mem_iInter.mpr hn
      change z ∈ (⋂ b, ((finiteProductOverLift C' j').left.imageι ≫
        (finiteProductOverπ C' b).left) ⁻¹'
          closure ((β b).left ⁻¹' ((E.V b).ι '' (E.q b ⁻¹' (E.W b : Set X)ᶜ)))) at hz
      rw [hempty] at hz
      exact hz
    obtain ⟨b, hb⟩ := hex
    apply Opens.mem_iSup.mpr
    refine ⟨b, ?_⟩
    change π b z ∈ (OY b : Set (C' b).left)
    rw [hOY b]
    exact hb
  refine ⟨E.U, P, pP, c, E.n, O, M, pM, x, k, a, E.dense, inferInstance,
    inferInstance, hc, hdc, hcp, hcover, ?_⟩
  intro b
  refine ⟨hM b, hsep b, hqc b, hlft b, hx b, hxd b, hxp b, ?_, haO b, ?_⟩
  · dsimp only [k]
    rw [Category.assoc, hop b, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, Category.assoc, (β b).w]
    simpa only [π, Category.assoc] using
      congrArg (fun z => (O b).ι ≫ z) (hπp b)
  · dsimp only [k]
    rw [← Category.assoc, har b, Category.assoc, ← hxr b, ← Category.assoc]
    dsimp only [inc]
    rw [Scheme.homOfLE_ι]

end AlgebraicGeometry.Scheme.Compactification
