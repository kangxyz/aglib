/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
/-!
# Sections on quasi-compact opens of an affine scheme

The finite-cover argument below clears finitely many local denominators and
finitely many overlap discrepancies, and then uses the actual sheaf gluing
axiom. It does not assume that an open-immersion pushforward is quasicoherent.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open PrimeSpectrum

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

/-- The explicit numerator and torsion conditions for localization of sections
on `V` at the element `f`. Both maps are actual sheaf restrictions. -/
structure ClearsDenominators (V : (Spec R).Opens) (f : R) : Prop where
  existence (s : Γ(M, V ⊓ PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)),
      M.presheaf.map (homOfLE inf_le_left).op t = f ^ n • s
  uniqueness (t : Γ(M, V)) :
    M.presheaf.map (homOfLE (inf_le_left : V ⊓ PrimeSpectrum.basicOpen f ≤ V)).op t = 0 →
    ∃ n : ℕ, f ^ n • t = 0

/-- The actual restriction map, with its canonical `R`-linear structure. -/
abbrev restriction (V : (Spec R).Opens) (f : R) :
    ((modulesSpecToSheaf.obj M).obj.obj (op V)) →ₗ[R]
      ((modulesSpecToSheaf.obj M).obj.obj (op (V ⊓ PrimeSpectrum.basicOpen f))) :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE inf_le_left).op).hom

lemma clearsDenominators_iff_isLocalized (V : (Spec R).Opens) (f : R) :
    ClearsDenominators M V f ↔ IsLocalizedModule.Away f (restriction M V f) := by
  constructor
  · intro h
    refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
    · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f inf_le_right
    · intro s
      obtain ⟨n, t, ht⟩ := h.existence s
      exact ⟨n, t, ht.symm⟩
    · intro t ht
      exact h.uniqueness t ht
  · intro h
    refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
    · obtain ⟨n, t, ht⟩ := h.surj _ _ s
      exact ⟨n, t, ht.symm⟩
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
        (IsLocalizedModule.eq_zero_iff (.powers f) (restriction M V f)).mp ht
      exact ⟨n, hn⟩

/-- Quasicoherence on a principal chart gives the numerator and torsion
conditions on that chart for every element of the original ring. -/
lemma clearsDenominators_basicOpen (g f : R)
    [((Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))))).obj M).IsQuasicoherent] :
    ClearsDenominators M (PrimeSpectrum.basicOpen g) f := by
  let a : R ⟶ CommRingCat.of (Localization.Away g) :=
    CommRingCat.ofHom (algebraMap R _)
  set ψ : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec R := Spec.map a
  set M' : (Spec (CommRingCat.of (Localization.Away g))).Modules := M.restrict ψ
  have h : IsLocalizing (modulesSpecToSheaf.obj M') :=
    (isIso_fromTildeΓ_iff_isLocalizing M').mp inferInstance
  have hf : IsLocalizedModule.Away (a f)
      ((modulesSpecToSheaf.obj M').obj.map (PrimeSpectrum.basicOpen (a f)).leTop.op).hom := h (a f)
  have heq : PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f =
      ψ ''ᵁ PrimeSpectrum.basicOpen (a f) := by
    rw [← SpecMap_preimage_basicOpen, Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [a, ψ]
  let iso : Γ(M', ⊤) ≅ Γ(M, PrimeSpectrum.basicOpen g) :=
    M.restrictAppIso ψ ⊤ ≪≫ M.presheaf.mapIso (eqToIso (by simp [ψ, a])).op
  let e : Γ(M', PrimeSpectrum.basicOpen (a f)) ≅
      Γ(M, PrimeSpectrum.basicOpen g ⊓ PrimeSpectrum.basicOpen f) :=
    M.restrictAppIso ψ (PrimeSpectrum.basicOpen (a f)) ≪≫ M.presheaf.mapIso (eqToIso heq).op
  refine ⟨fun s ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨n, t, ht⟩ := hf.surj _ _ (e.inv s)
    refine ⟨n, iso.hom t, ?_⟩
    have ht' := ht.symm
    change M'.presheaf.map (PrimeSpectrum.basicOpen (a f)).leTop.op t = _ at ht'
    have hh := congr(e.hom $ht')
    dsimp [M'] at hh
    rw [← ConcreteCategory.comp_apply] at hh
    simp only [homOfLE_leOfHom, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv, e, iso] at hh ⊢
    simp only [homOfLE_leOfHom, Scheme.Modules.map_restrictAppIso_hom_assoc,
      AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, ← map_pow, ψ] at hh
    rw [_root_.AlgebraicGeometry.Scheme.Modules.restrictAppIso_smul_Spec] at hh
    simpa [← Functor.map_comp_apply, eqToHom_comp_homOfLE_op, homOfLE_op_comp_eqToHom] using hh
  · have hz : M'.presheaf.map (PrimeSpectrum.basicOpen (a f)).leTop.op (iso.inv t) = 0 := by
      simpa [M', iso, ← M.presheaf.map_comp_apply, homOfLE_op_comp_eqToHom, e] using
        congr(e.inv $ht)
    have hz' : ((modulesSpecToSheaf.obj M').obj.map
        (PrimeSpectrum.basicOpen (a f)).leTop.op).hom (iso.inv t) = 0 := hz
    obtain ⟨n, hn⟩ := hf.exists_of_eq (a f)
      (x := iso.inv t) (y := 0) (by simpa only [map_zero] using hz')
    simp only [smul_zero] at hn
    refine ⟨n, ?_⟩
    have hh := congr(iso.hom $hn)
    dsimp [iso, ψ] at hh
    rw [eqToHom_op, map_zero, ← map_pow,
      _root_.AlgebraicGeometry.Scheme.Modules.restrictAppIso_smul_Spec,
      M.map_smul_Spec, Iso.inv_hom_id_apply] at hh
    simpa using hh

/-- The explicit denominator and torsion conditions glue across a finite open
cover. Clearing the overlap torsion is essential: chosen local numerators
need not agree before the additional common power is applied. -/
lemma ClearsDenominators.of_finite_cover (V : (Spec R).Opens) (f : R)
    {ι : Type*} [Finite ι] (U : ι → (Spec R).Opens) (hV : V = ⨆ i, U i)
    (h₁ : ∀ i, ClearsDenominators M (U i) f)
    (h₂ : ∀ i j, ClearsDenominators M (U i ⊓ U j) f) :
    ClearsDenominators M V f := by
  have hle (i : ι) : U i ≤ V := by rw [hV]; exact le_iSup_of_le _ le_rfl
  refine ⟨fun s ↦ ?_, fun t hs ↦ ?_⟩
  · let s' (i : ι) : Γ(M, U i ⊓ PrimeSpectrum.basicOpen f) :=
      M.presheaf.map (homOfLE (inf_le_inf (hle i) le_rfl)).op s
    obtain ⟨N, t, ht⟩ : ∃ (N : ℕ) (t : ∀ i, Γ(M, U i)),
        ∀ i, f ^ N • s' i = M.presheaf.map (homOfLE inf_le_left).op (t i) := by
      choose n t ht using fun i ↦ (h₁ i).existence (s' i)
      refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t i, fun i ↦ ?_⟩
      have hn : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by omega
      conv_lhs => rw [hN]
      rw [pow_add, mul_smul, ← ht i, M.map_smul_Spec]
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ i j,
        M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (f ^ K • t i) =
          M.presheaf.map (homOfLE inf_le_right).op (f ^ K • t j) := by
      have h (i j : ι) : ∃ k : ℕ,
          M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (f ^ k • t i) =
            M.presheaf.map (homOfLE inf_le_right).op (f ^ k • t j) := by
        have hz : M.presheaf.map
            (homOfLE (inf_le_left : (U i ⊓ U j) ⊓ PrimeSpectrum.basicOpen f ≤ U i ⊓ U j)).op
            (M.presheaf.map (homOfLE inf_le_left).op (t i) -
              M.presheaf.map (homOfLE inf_le_right).op (t j)) = 0 := by
          have hi : (U i ⊓ U j) ⊓ PrimeSpectrum.basicOpen f ≤ U i ⊓ PrimeSpectrum.basicOpen f :=
            inf_le_inf inf_le_left le_rfl
          have hj : (U i ⊓ U j) ⊓ PrimeSpectrum.basicOpen f ≤ U j ⊓ PrimeSpectrum.basicOpen f :=
            inf_le_inf inf_le_right le_rfl
          rw [map_sub, ← M.presheaf.map_comp_apply, ← op_comp,
            ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, homOfLE_comp,
            ← homOfLE_comp hi inf_le_left, ← homOfLE_comp hj inf_le_left,
            op_comp, M.presheaf.map_comp_apply, ← ht i, M.map_smul_Spec,
            op_comp, M.presheaf.map_comp_apply, ← ht j, M.map_smul_Spec]
          simp only [s', ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, sub_self]
        obtain ⟨k, hk⟩ := (h₂ i j).uniqueness _ hz
        refine ⟨k, ?_⟩
        simpa only [smul_sub, sub_eq_zero, M.map_smul_Spec] using hk
      choose k hk using h
      let K := ⨆ i, ⨆ j, k i j
      refine ⟨K, fun i j ↦ ?_⟩
      have hkK : k i j ≤ K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have hK : K = (K - k i j) + k i j := by omega
      rw [hK, pow_add, mul_smul, mul_smul, M.map_smul_Spec,
        M.map_smul_Spec _ (f ^ (K - k i j)), hk i j]
    obtain ⟨a, ha, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ U V
      (fun i ↦ homOfLE (hle i)) (by simp [hV]) (fun i ↦ f ^ K • t i) (by
        intro i j
        exact hK i j)
    refine ⟨N + K, a, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩
      (fun i ↦ U i ⊓ PrimeSpectrum.basicOpen f) (V ⊓ PrimeSpectrum.basicOpen f)
      (fun i ↦ homOfLE (inf_le_inf (hle i) le_rfl))
    · simp only [hV, iSup_inf_eq, le_refl]
    · intro i
      rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
        ← homOfLE_comp inf_le_left (hle i), op_comp, M.presheaf.map_comp_apply,
        ha, M.map_smul_Spec, ← ht i, M.map_smul_Spec, pow_add, mul_smul, smul_comm]
  · have h (i : ι) : ∃ n : ℕ,
        M.presheaf.map (homOfLE (hle i)).op (f ^ n • t) = 0 := by
      have hz : M.presheaf.map (homOfLE (inf_le_left : U i ⊓ PrimeSpectrum.basicOpen f ≤ U i)).op
          (M.presheaf.map (homOfLE (hle i)).op t) = 0 := by
        rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp (inf_le_inf (hle i) le_rfl) inf_le_left,
          op_comp, M.presheaf.map_comp_apply, hs, map_zero]
      obtain ⟨n, hn⟩ := (h₁ i).uniqueness _ hz
      exact ⟨n, by rw [M.map_smul_Spec]; exact hn⟩
    choose n hn using h
    refine ⟨⨆ i, n i, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ U V
      (fun i ↦ homOfLE (hle i)) (by simp [hV])
    intro i
    have hnN : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
    have hN : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by omega
    rw [hN, pow_add, mul_smul, M.map_smul_Spec, hn i]
    simp

/-- On a quasi-compact open of an affine scheme, principal-chart
quasicoherence implies localization of actual sections. -/
lemma isLocalized_of_principal_charts (V : (Spec R).Opens) (hV : IsCompact (V : Set (Spec R)))
    (hM : ∀ (g : R), PrimeSpectrum.basicOpen g ≤ V →
      ((Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))))).obj M).IsQuasicoherent)
    (f : R) : IsLocalizedModule.Away f (restriction M V f) := by
  obtain ⟨ι, _, g, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact V hV
  have hle (i : ι) : PrimeSpectrum.basicOpen (g i) ≤ V := by rw [hg]; exact le_iSup_of_le _ le_rfl
  apply (clearsDenominators_iff_isLocalized M V f).mp
  apply ClearsDenominators.of_finite_cover M V f (fun i ↦ PrimeSpectrum.basicOpen (g i)) hg
  · intro i
    have := hM (g i) (hle i)
    exact clearsDenominators_basicOpen M (g i) f
  · intro i j
    rw [← PrimeSpectrum.basicOpen_mul]
    have := hM (g i * g j) ((PrimeSpectrum.basicOpen_mul_le_left _ _).trans (hle i))
    exact clearsDenominators_basicOpen M (g i * g j) f

/-- Restricting a quasicoherent sheaf on an open to any contained principal
chart remains quasicoherent. This is a composition of genuine restrictions. -/
lemma principal_chart_quasicoherent_of_restrict (V : (Spec R).Opens)
    [(M.restrict V.ι).IsQuasicoherent] (g : R) (hg : PrimeSpectrum.basicOpen g ≤ V) :
    ((Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))))).obj M).IsQuasicoherent :=
        by
  let t := (Spec R).homOfLE (U := PrimeSpectrum.basicOpen g) (V := V) hg
  let q := (basicOpenIsoSpecAway g).inv ≫ t
  let e : Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.restrictFunctor q ≅
      Scheme.Modules.restrictFunctor
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))) :=
    (Scheme.Modules.restrictFunctorComp q V.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by simp [q, t, basicOpenIsoSpecAway])
  have hq : ((M.restrict V.ι).restrict q).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent
    (Spec (CommRingCat.of (Localization.Away g))).ringCatSheaf).prop_of_iso (e.app M) hq

/-- For a sheaf quasicoherent on a quasi-compact open `V`, the canonical
restriction `Γ(V,M) → Γ(V ∩ D(f),M)` is localization at `f`. No quasicoherence
of `M` outside `V` is assumed. -/
theorem isLocalized_of_isCompact (V : (Spec R).Opens) (hV : IsCompact (V : Set (Spec R)))
    [(M.restrict V.ι).IsQuasicoherent] (f : R) :
    IsLocalizedModule.Away f (restriction M V f) :=
  isLocalized_of_principal_charts M V hV
    (principal_chart_quasicoherent_of_restrict M V) f

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections
