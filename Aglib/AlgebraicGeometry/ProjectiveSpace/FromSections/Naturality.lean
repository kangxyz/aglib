/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# Source naturality of the projective morphism from original sections

The original finite family is pulled through the native unit and free-module
comparisons. Actual pulled frames retain the original coefficient functions,
so their projective chart maps are the original chart maps after composition.
Change of line-module coordinates also preserves the resulting morphism.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MvPolynomial Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpace.FromSections

variable {R : Type u} [CommRing R] {I : Type u} {X T : Scheme.{u}}

/-- Pull the original section map through the actual structure-module comparison. -/
def pullbackSection (g : T ⟶ X) {M : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    SheafOfModules.unit T.ringCatSheaf ⟶ (Scheme.Modules.pullback g).obj M :=
  (pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map s

/-- The pulled original family retains its literal coordinate index. -/
def pulledFamily (g : T ⟶ X) {M : X.Modules}
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M)) :
    I → (SheafOfModules.unit T.ringCatSheaf ⟶ (Scheme.Modules.pullback g).obj M) :=
  fun i => pullbackSection g (s i)

theorem pulledFamily_desc (g : T ⟶ X) {M : X.Modules}
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M)) :
    Sigma.desc (pulledFamily g s) =
      (pullbackFreeIso g I).inv ≫ (Scheme.Modules.pullback g).map (Sigma.desc s) := by
  apply (cancel_epi (pullbackFreeIso g I).hom).mp
  refine Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback g) _ _
      (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)) _ _ (fun i => ?_)
  change (Scheme.Modules.pullback g).map (SheafOfModules.ιFree i) ≫ _ =
    (Scheme.Modules.pullback g).map (SheafOfModules.ιFree i) ≫ _
  simp only [Iso.hom_inv_id_assoc]
  erw [SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom_assoc]
  change (pullbackUnitIso g).hom ≫ SheafOfModules.ιFree i ≫
      Sigma.desc (pulledFamily g s) =
    (Scheme.Modules.pullback g).map (SheafOfModules.ιFree i) ≫
      (Scheme.Modules.pullback g).map (Sigma.desc s)
  rw [SheafOfModules.ιFree, Sigma.ι_comp_desc]
  change (pullbackUnitIso g).hom ≫ (pullbackUnitIso g).inv ≫
      (Scheme.Modules.pullback g).map (s i) = _
  rw [Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp]
  exact congrArg (Scheme.Modules.pullback g).map (Sigma.ι_comp_desc s i).symm

/-- Pullback preserves generation of the same original family, without flatness. -/
instance pulledFamily_epi (g : T ⟶ X) {M : X.Modules}
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M)) [Epi (Sigma.desc s)] :
    Epi (Sigma.desc (pulledFamily g s)) := by
  let : (Scheme.Modules.pullback g).PreservesEpimorphisms :=
    CategoryTheory.Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction g)
  rw [pulledFamily_desc]
  infer_instance

/-- The literal pulled unit-map section is the native adjunction-unit section. -/
theorem pullbackSection_global (g : T ⟶ X) {M : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    unitHomGlobalSectionsEquiv T _ (pullbackSection g s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤)
        (unitHomGlobalSectionsEquiv X M s) := by
  have h : SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map (pullbackSection g s) =
      s ≫ (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M := by
    rw [← pullbackUnitIso_homEquiv g, ← Adjunction.homEquiv_naturality_right]
    simp only [pullbackSection, Iso.hom_inv_id_assoc]
    rw [Adjunction.homEquiv_unit]
    exact (Scheme.Modules.pullbackPushforwardAdjunction g).unit_naturality s
  have he := congrArg (fun f => f.val.app (op ⊤) (1 : Γ(X, ⊤))) h
  change (pullbackSection g s).val.app (op ⊤) ((g.appTop).hom 1) = _ at he
  rw [map_one] at he
  exact he

namespace SectionFrames

variable {M N : X.Modules} {s : I → M.sections} {t : I → N.sections}
  (F : SectionFrames M s) (G : SectionFrames N t)

/-- Original coefficients in two actual frames differ by their displayed generator ratio. -/
theorem coefficientOn_iso (e : M ≅ N)
    (hs : ∀ j (O : X.Opens), e.hom.val.app (op O) ((s j).val (op O)) =
      (t j).val (op O))
    (k : F.K) (l : G.K) {O : X.Opens} (hk : O ≤ F.U k) (hl : O ≤ G.U l) (j : I) :
    F.coefficientOn k hk j =
      F.coefficientOn k hk (G.coordinate l) * G.coefficientOn l hl j := by
  have h : (show Γ(M, O) from (s j).val (op O)) =
      G.coefficientOn l hl j • (show Γ(M, O) from (s (G.coordinate l)).val (op O)) := by
    apply (((SheafOfModules.evaluation X.ringCatSheaf (op O)).mapIso e).toLinearEquiv).injective
    rw [_root_.map_smul]
    change e.hom.val.app (op O) ((s j).val (op O)) =
      G.coefficientOn l hl j •
        (show Γ(N, O) from e.hom.val.app (op O) ((s (G.coordinate l)).val (op O)))
    rw [hs, hs, G.selected_eq_generator]
    exact (LocalFrames.coefficient_smul_generator G.U N G.frame l hl
      ((t j).val (op O))).symm
  have hh := congrArg (LocalFrames.coefficient F.U M F.frame k hk) h
  rw [_root_.map_smul, smul_eq_mul, mul_comm] at hh
  exact hh

/-- Actual section-preserving change of line-module coordinates preserves the projective map. -/
theorem map_eq_of_iso (p : X ⟶ Spec (CommRingCat.of R)) (e : M ≅ N)
    (hs : ∀ j (O : X.Opens), e.hom.val.app (op O) ((s j).val (op O)) =
      (t j).val (op O)) : F.map p = G.map p := by
  let V : F.K × G.K → X.Opens := fun z => F.U z.1 ⊓ G.U z.2
  have hV : iSup V = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show x ∈ iSup F.U by rw [F.covers]; trivial)
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp (show x ∈ iSup G.U by rw [G.covers]; trivial)
    exact Opens.mem_iSup.mpr ⟨(k,l), hk, hl⟩
  apply (X.openCoverOfIsOpenCover V (.mk hV)).hom_ext
  intro z
  change (V z).ι ≫ F.map p = (V z).ι ≫ G.map p
  rw [F.ι_map_on p z.1 inf_le_left, G.ι_map_on p z.2 inf_le_right]
  unfold chartMap
  apply congrArg (fun q => (V z).toSpecΓ ≫ q)
  apply FiniteEmbedding.chart_maps_eq_of_rescaling
  · intro r
    rw [chartRingHom_coefficient, chartRingHom_coefficient]
  · rw [chartRingHom_ratio]
    have h := F.coefficientOn_iso G e hs z.1 z.2 inf_le_left inf_le_right (F.coordinate z.1)
    rw [F.coefficientOn_selected] at h
    exact isUnit_iff_exists_inv.mpr ⟨G.coefficientOn z.2 inf_le_right (F.coordinate z.1), h.symm⟩
  · intro j
    rw [chartRingHom_ratio, chartRingHom_ratio, chartRingHom_ratio]
    exact F.coefficientOn_iso G e hs z.1 z.2 inf_le_left inf_le_right j

end SectionFrames

section CocycleSections

variable {J : Type u} {U : J → X.Opens} (g : T ⟶ X) (c : UnitCocycle U)

/-- The actual pulled-cocycle comparison retains the pulled coefficient
of an original section. -/
theorem pullbackCocycleIso_section_coefficient (hU : iSup U = ⊤)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ c.sheaf)
    (k : J) {O : T.Opens} (hk : O ≤ g ⁻¹ᵁ U k) :
    (pullbackCocycle g c).localSectionsEquiv k hk
        ((pullbackCocycleIso g c hU).hom.val.app (op O)
          ((pullbackSection g s).val.app (op O) (1 : Γ(T, O)))) =
      (g.appLE (U k) O hk).hom
        (c.localSectionsEquiv k le_rfl (s.val.app (op (U k)) (1 : Γ(X, U k)))) := by
  let a := unitHomGlobalSectionsEquiv X c.sheaf s
  have ht := pulledGlobalSection_restrict g c a k hk
  have hs0 : pulledGlobalSection g c a =
      unitHomGlobalSectionsEquiv T _ (pullbackSection g s) :=
    (pullbackSection_global g s).symm
  have hs : (pullbackSection g s).val.app (op O) (1 : Γ(T, O)) =
      ((Scheme.Modules.pullback g).obj c.sheaf).val.map (homOfLE le_top).op
        (pulledGlobalSection g c a) := by
    rw [hs0]
    exact (PresheafOfModules.sections_property
      (((Scheme.Modules.pullback g).obj c.sheaf).unitHomEquiv (pullbackSection g s))
        (homOfLE (show O ≤ ⊤ from le_top)).op).symm
  rw [hs, ht, _root_.map_smul]
  rw [pullbackCocycleIso,
    UnitCocycle.pullbackIso_hom_pullbackGenerator g c (pullbackCocycle g c)
      (fun _ => rfl) (pullbackCocycle_transition g c) hU k hk,
    _root_.map_smul, UnitCocycle.localSectionsEquiv_generator, smul_eq_mul, mul_one]
  congr 2
  exact PresheafOfModules.sections_property (c.sheaf.unitHomEquiv s)
    (homOfLE (show U k ≤ ⊤ from le_top)).op

end CocycleSections

namespace SectionFrames

variable {M : X.Modules} {s : I → M.sections} (F : SectionFrames M s) (g : T ⟶ X)

/-- The unit cocycle of the original supplied module frames. -/
abbrev frameCocycle := LocalFrames.cocycle F.U M F.frame

/-- Reconstruction of the original module from its actual frame cocycle. -/
abbrev frameCocycleIso := LocalFrames.sheafIso F.U M F.frame F.covers

theorem frameCocycleIso_inv_coefficient (k : F.K) {O : X.Opens}
    (hk : O ≤ F.U k) (t : Γ(M, O)) :
    F.frameCocycle.localSectionsEquiv k hk
        (F.frameCocycleIso.inv.val.app (op O) t) =
      LocalFrames.coefficient F.U M F.frame k hk t := by
  have he : (SheafOfModules.overFunctor X.ringCatSheaf (F.U k)).map
        F.frameCocycleIso.inv ≫ (F.frameCocycle.localIso k).hom = (F.frame k).hom := by
    apply (cancel_epi ((SheafOfModules.overFunctor X.ringCatSheaf (F.U k)).map
      F.frameCocycleIso.hom)).mp
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [LocalFrames.sheafIso_hom_over]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun f => f.val.app (op (Over.mk (homOfLE hk))) t) he

/-- The genuine pullback of the original module in its original frame cocycle. -/
def pulledFrameIso : (Scheme.Modules.pullback g).obj M ≅
    (pullbackCocycle g F.frameCocycle).sheaf :=
  (Scheme.Modules.pullback g).mapIso F.frameCocycleIso.symm ≪≫
    pullbackCocycleIso g F.frameCocycle F.covers

/-- Original frames pulled to the actual inverse-image opens. -/
def pulledFrame (k : F.K) : ((Scheme.Modules.pullback g).obj M).over (g ⁻¹ᵁ F.U k) ≅
    SheafOfModules.unit (T.ringCatSheaf.over (g ⁻¹ᵁ F.U k)) :=
  (SheafOfModules.overFunctor T.ringCatSheaf (g ⁻¹ᵁ F.U k)).mapIso (F.pulledFrameIso g) ≪≫
    (pullbackCocycle g F.frameCocycle).localIso k

theorem pulledFrame_coefficient (k : F.K) {O : T.Opens} (hk : O ≤ g ⁻¹ᵁ F.U k) (j : I) :
    LocalFrames.coefficient (fun k => g ⁻¹ᵁ F.U k) ((Scheme.Modules.pullback g).obj M)
        (F.pulledFrame g) k hk
          ((((Scheme.Modules.pullback g).obj M).unitHomEquiv
            (pullbackSection g (M.unitHomEquiv.symm (s j)))).val (op O)) =
      (g.appLE (F.U k) O hk).hom (F.coefficientOn k le_rfl j) := by
  have ht : pullbackSection g (M.unitHomEquiv.symm (s j)) ≫ (F.pulledFrameIso g).hom =
      pullbackSection g (M.unitHomEquiv.symm (s j) ≫ F.frameCocycleIso.inv) ≫
        (pullbackCocycleIso g F.frameCocycle F.covers).hom := by
    simp only [pullbackSection, pulledFrameIso, Functor.mapIso_hom, Iso.trans_hom,
      Iso.symm_hom, Functor.map_comp, Category.assoc]
  have htv := congrArg (fun f => f.val.app (op O) (1 : Γ(T, O))) ht
  change (F.pulledFrameIso g).hom.val.app (op O)
      ((pullbackSection g (M.unitHomEquiv.symm (s j))).val.app (op O) (1 : Γ(T, O))) =
    (pullbackCocycleIso g F.frameCocycle F.covers).hom.val.app (op O)
      ((pullbackSection g (M.unitHomEquiv.symm (s j) ≫ F.frameCocycleIso.inv)).val.app
        (op O) (1 : Γ(T, O))) at htv
  change (pullbackCocycle g F.frameCocycle).localSectionsEquiv k hk
      ((F.pulledFrameIso g).hom.val.app (op O)
        ((pullbackSection g (M.unitHomEquiv.symm (s j))).val.app (op O)
          (1 : Γ(T, O)))) = _
  rw [htv]
  rw [pullbackCocycleIso_section_coefficient g F.frameCocycle F.covers]
  congr 1
  change F.frameCocycle.localSectionsEquiv k le_rfl
      (F.frameCocycleIso.inv.val.app (op (F.U k))
        ((M.unitHomEquiv (M.unitHomEquiv.symm (s j))).val (op (F.U k)))) = _
  rw [Equiv.apply_symm_apply]
  exact F.frameCocycleIso_inv_coefficient k le_rfl _

/-- A genuine pulled frame cover, normalized by the same originally selected sections. -/
def pullback : SectionFrames ((Scheme.Modules.pullback g).obj M)
    (fun j => ((Scheme.Modules.pullback g).obj M).unitHomEquiv
      (pullbackSection g (M.unitHomEquiv.symm (s j)))) where
  K := F.K
  U k := g ⁻¹ᵁ F.U k
  covers := by rw [← Scheme.Hom.preimage_iSup, F.covers, Scheme.Hom.preimage_top]
  coordinate := F.coordinate
  frame := F.pulledFrame g
  selected k := by rw [F.pulledFrame_coefficient g, F.coefficientOn_selected, map_one]

theorem pullback_coefficientOn (k : F.K) {O : T.Opens} (hk : O ≤ g ⁻¹ᵁ F.U k) (j : I) :
    (F.pullback g).coefficientOn k hk j =
      (g.appLE (F.U k) O hk).hom (F.coefficientOn k le_rfl j) :=
  F.pulledFrame_coefficient g k hk j

theorem pullback_chartRingHom (p : X ⟶ Spec (CommRingCat.of R)) (k : F.K) :
    (F.pullback g).chartRingHom (g ≫ p) k le_rfl =
      (g.app (F.U k)).hom.comp (F.chartRingHom p k le_rfl) := by
  have hb : baseCoefficient (g ≫ p) (g ⁻¹ᵁ F.U k) =
      (g.app (F.U k)).hom.comp (baseCoefficient p (F.U k)) := by
    ext r
    change (((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫ g.appTop) ≫
        T.presheaf.map (homOfLE le_top).op).hom r =
      (((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop ≫
        X.presheaf.map (homOfLE le_top).op) ≫ g.app (F.U k)).hom r
    simp only [Category.assoc]
    rw [Scheme.Hom.naturality]
    rfl
  have hv : (fun j : {j : I // j ≠ F.coordinate k} =>
      (F.pullback g).coefficientOn k le_rfl j.1) =
      (fun j => (g.app (F.U k)).hom (F.coefficientOn k le_rfl j.1)) := by
    funext j
    exact (F.pullback_coefficientOn g k le_rfl j.1).trans
      (congrArg (fun f : Γ(X, F.U k) ⟶ Γ(T, g ⁻¹ᵁ F.U k) =>
        f.hom (F.coefficientOn k le_rfl j.1)) g.appLE_eq_app)
  change (eval₂Hom (baseCoefficient (g ≫ p) (g ⁻¹ᵁ F.U k))
      (fun j : {j : I // j ≠ F.coordinate k} =>
        (F.pullback g).coefficientOn k le_rfl j.1)).comp
          (coordinateRingToPolynomial R I (F.coordinate k)) =
    (g.app (F.U k)).hom.comp
      ((eval₂Hom (baseCoefficient p (F.U k))
        (fun j : {j : I // j ≠ F.coordinate k} => F.coefficientOn k le_rfl j.1)).comp
          (coordinateRingToPolynomial R I (F.coordinate k)))
  rw [← RingHom.comp_assoc, MvPolynomial.comp_eval₂Hom, hb]
  exact congrArg (fun v : {j : I // j ≠ F.coordinate k} → Γ(T, g ⁻¹ᵁ F.U k) =>
    (eval₂Hom ((g.app (F.U k)).hom.comp (baseCoefficient p (F.U k))) v).comp
      (coordinateRingToPolynomial R I (F.coordinate k))) hv

/-- The actual pulled-frame morphism is composition of the original morphism. -/
theorem pullback_map (p : X ⟶ Spec (CommRingCat.of R)) :
    g ≫ F.map p = (F.pullback g).map (g ≫ p) := by
  apply (F.pullback g).sourceOpenCover.hom_ext
  intro k
  change F.K at k
  change (g ⁻¹ᵁ F.U k).ι ≫ g ≫ F.map p =
    (g ⁻¹ᵁ F.U k).ι ≫ (F.pullback g).map (g ≫ p)
  calc
    _ = g ∣_ F.U k ≫ F.chartMap p k le_rfl := by
      rw [← morphismRestrict_ι_assoc, F.ι_map]
    _ = (F.pullback g).chartMap (g ≫ p) k le_rfl := by
      unfold chartMap
      rw [F.pullback_chartRingHom g p k]
      change _ = (g ⁻¹ᵁ F.U k).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (F.chartRingHom p k le_rfl) ≫ g.app (F.U k)) ≫ _
      rw [Spec.map_comp]
      simp only [Category.assoc]
      rw [Scheme.Opens.toSpecΓ_naturality_assoc]
      rfl
    _ = _ := ((F.pullback g).ι_map (g ≫ p) k).symm

end SectionFrames

/-- An actual section-preserving module isomorphism preserves the constructed projective map. -/
theorem mapOfFiniteFamily_iso (p : X ⟶ Spec (CommRingCat.of R))
    (M N : X.Modules) (hM : IsLocallyRankOne X M) (hN : IsLocallyRankOne X N)
    [Finite I] (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M))
    (t : I → (SheafOfModules.unit X.ringCatSheaf ⟶ N))
    [Epi (Sigma.desc s)] [Epi (Sigma.desc t)]
    (e : M ≅ N) (hs : ∀ j, s j ≫ e.hom = t j) :
    mapOfFiniteFamily p M hM s = mapOfFiniteFamily p N hN t := by
  apply SectionFrames.map_eq_of_iso _ _ p e
  intro j O
  simp only [generatingSectionsOfFamily_section]
  exact congrArg (fun f => (N.unitHomEquiv f).val (op O)) (hs j)

/-- Pulling the original finite generating family commutes with its actual projective morphism. -/
theorem mapOfFiniteFamily_pullback (g : T ⟶ X) (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M) [Finite I]
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M)) [Epi (Sigma.desc s)] :
    g ≫ mapOfFiniteFamily p M hM s =
      mapOfFiniteFamily (g ≫ p) ((Scheme.Modules.pullback g).obj M)
        (pullback_locallyRankOne g M hM) (pulledFamily g s) := by
  let F := framesOfGeneratingSections M hM (generatingSectionsOfFamily s)
  refine (F.pullback_map g p).trans ?_
  apply SectionFrames.map_eq_of_iso _ _ (g ≫ p) (Iso.refl _)
  intro j O
  simp only [Iso.refl_hom, generatingSectionsOfFamily_section]
  have hs : pullbackSection g (M.unitHomEquiv.symm (M.unitHomEquiv (s j))) ≫
      𝟙 ((Scheme.Modules.pullback g).obj M) = pulledFamily g s j := by
    rw [Equiv.symm_apply_apply, Category.comp_id]
    rfl
  exact congrArg (fun f => (((Scheme.Modules.pullback g).obj M).unitHomEquiv f).val (op O)) hs

/-- Generation is retained after composing the original section maps with an actual isomorphism. -/
instance family_comp_iso_epi {M N : X.Modules}
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M)) [Epi (Sigma.desc s)] (e : M ≅ N) :
    Epi (Sigma.desc (fun i => s i ≫ e.hom)) := by
  have h : Sigma.desc (fun i => s i ≫ e.hom) = Sigma.desc s ≫ e.hom := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
  rw [h]
  infer_instance

/-- Source naturality also retains an actual comparison with any isomorphic target module. -/
theorem mapOfFiniteFamily_pullback_iso (g : T ⟶ X) (p : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (hM : IsLocallyRankOne X M) [Finite I]
    (s : I → (SheafOfModules.unit X.ringCatSheaf ⟶ M)) [Epi (Sigma.desc s)]
    (N : T.Modules) (e : (Scheme.Modules.pullback g).obj M ≅ N) :
    g ≫ mapOfFiniteFamily p M hM s =
      mapOfFiniteFamily (g ≫ p) N
        (isLocallyRankOne_of_iso T e (pullback_locallyRankOne g M hM))
        (fun i => pulledFamily g s i ≫ e.hom) :=
  (mapOfFiniteFamily_pullback g p M hM s).trans
    (mapOfFiniteFamily_iso (g ≫ p) _ N (pullback_locallyRankOne g M hM) _
      (pulledFamily g s) _ e (fun _ => rfl))

end AlgebraicGeometry.ProjectiveSpace.FromSections
