/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Modules.Maps
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# Actual properties of finitely presented stage modules

Eventual invertibility descends an actual inverse and both inverse equations.
Specified relative isomorphisms retain their original forward and inverse
triangle equations. Local rank one is detected through genuine finite
trivializing affine covers and their actual frame isomorphisms.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A given map of finitely presented stage modules becomes an isomorphism
at a later stage when its actual limit pullback is an isomorphism. The
proof descends an actual inverse and its two inverse equations. -/
theorem exists_isIso_pullback_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (f : M ⟶ N) [IsIso ((pullback (c.π.app i)).map f)] :
    ∃ (j : I) (q : j ⟶ i), IsIso ((pullback (D.map q)).map f) := by
  let e := asIso ((pullback (c.π.app i)).map f)
  obtain ⟨j, q, g, hg⟩ := exists_hom_above_of_isLimit D c hc i N M e.inv
  let U := pullbackConeCompIso D c q
  let P := (pullback (D.map q)).obj M
  let Q := (pullback (D.map q)).obj N
  let f' : P ⟶ Q := (pullback (D.map q)).map f
  let e' : (pullback (c.π.app j)).obj P ≅ (pullback (c.π.app j)).obj Q :=
    (U.app M).symm ≪≫ e ≪≫ U.app N
  have hf' : (pullback (c.π.app j)).map f' = e'.hom := by
    apply (cancel_epi (U.hom.app M)).mp
    have hnat := (U.hom.naturality f).symm
    simpa only [Functor.comp_map, f', e, asIso_hom, e', Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc] using hnat
  have hg' : (pullback (c.π.app j)).map g = e'.inv := by
    apply (cancel_epi (U.hom.app N)).mp
    simpa only [e', Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
      Category.assoc, Iso.hom_inv_id_app_assoc] using hg
  have hl : (pullback (c.π.app j)).map (f' ≫ g) =
      (pullback (c.π.app j)).map (𝟙 P) := by
    rw [Functor.map_comp, hf', hg', e'.hom_inv_id, CategoryTheory.Functor.map_id]
  have hr : (pullback (c.π.app j)).map (g ≫ f') =
      (pullback (c.π.app j)).map (𝟙 Q) := by
    rw [Functor.map_comp, hg', hf', e'.inv_hom_id, CategoryTheory.Functor.map_id]
  obtain ⟨k₁, r₁, hk₁⟩ := exists_hom_equality_above_of_isLimit D c hc j P P (f' ≫ g) (𝟙 P) hl
  obtain ⟨k₂, r₂, hk₂⟩ := exists_hom_equality_above_of_isLimit D c hc j Q Q (g ≫ f') (𝟙 Q) hr
  obtain ⟨k, s₁, s₂, hs⟩ := IsCofiltered.cospan r₁ r₂
  let r : k ⟶ j := s₁ ≫ r₁
  let B := pullback (D.map r)
  have hleft : B.map (f' ≫ g) = B.map (𝟙 P) := by
    apply pullback_map_eq_of_eq (D.map_comp s₁ r₁).symm
    exact pullback_map_eq_of_comp (D.map s₁) (D.map r₁) hk₁
  have hright : B.map (g ≫ f') = B.map (𝟙 Q) := by
    have heq : D.map s₂ ≫ D.map r₂ = D.map r := by
      rw [← D.map_comp, ← hs]
    apply pullback_map_eq_of_eq heq
    exact pullback_map_eq_of_comp (D.map s₂) (D.map r₂) hk₂
  have : IsIso (B.map f') :=
    ⟨⟨B.map g, by simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using hleft,
      by simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using hright⟩⟩
  let V : pullback (D.map (r ≫ q)) ≅ pullback (D.map q) ⋙ B :=
    pullbackCongr (D.map_comp r q) ≪≫ (pullbackComp (D.map r) (D.map q)).symm
  have hV : IsIso ((pullback (D.map q) ⋙ B).map f) := by
    change IsIso (B.map f')
    infer_instance
  exact ⟨k, r ≫ q, (NatIso.isIso_map_iff V f).mpr hV⟩


private theorem pullbackHomOfTriangle_inv_eq
    {X Y S : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ S) (d : X ⟶ S) (h : a ≫ b = d)
    {M N : S.Modules} (e' : (pullback b).obj M ≅ (pullback b).obj N)
    (e : (pullback d).obj M ≅ (pullback d).obj N)
    (he : pullbackHomOfTriangle a b d h e'.hom = e.hom) :
    pullbackHomOfTriangle a b d h e'.inv = e.inv := by
  let T := pullbackTriangleIso a b d h
  let E : (pullback d).obj M ≅ (pullback d).obj N :=
    (T.app M).symm ≪≫ (pullback a).mapIso e' ≪≫ T.app N
  have hE : E.hom = e.hom := by
    simpa only [E, T, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.app_hom, Iso.app_inv, pullbackHomOfTriangle, Category.assoc] using he
  have hEq : E = e := Iso.ext hE
  have hInv := congrArg Iso.inv hEq
  simpa only [E, T, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv, pullbackHomOfTriangle, Category.assoc] using hInv

/-- A specified relative isomorphism descends with BOTH its original hom and
inverse, through the actual coefficient map and original cone triangles. -/
theorem exists_relative_iso_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) {S : Scheme.{u}}
    (t : D ⟶ (Functor.const I).obj S) (l : c.pt ⟶ S)
    (hl : ∀ i, c.π.app i ≫ t.app i = l) (i : I)
    (M N : S.Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (e : (pullback l).obj M ≅ (pullback l).obj N) :
    ∃ (j : I) (_ : j ⟶ i)
      (e' : (pullback (t.app j)).obj M ≅ (pullback (t.app j)).obj N),
      pullbackHomOfTriangle (c.π.app j) (t.app j) l (hl j) e'.hom = e.hom ∧
      pullbackHomOfTriangle (c.π.app j) (t.app j) l (hl j) e'.inv = e.inv := by
  obtain ⟨j, q, g, hg⟩ := exists_relative_hom_above_of_isLimit D c hc t l hl i M N e.hom
  let T := pullbackTriangleIso (c.π.app j) (t.app j) l (hl j)
  have hmap : (pullback (c.π.app j)).map g = T.hom.app M ≫ e.hom ≫ T.inv.app N := by
    apply (cancel_epi (T.inv.app M)).mp
    apply (cancel_mono (T.hom.app N)).mp
    simpa only [pullbackHomOfTriangle, Category.assoc, Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id_app, Category.comp_id] using hg
  have : IsIso ((pullback (c.π.app j)).map g) := by rw [hmap]; infer_instance
  obtain ⟨k, r, hr⟩ := exists_isIso_pullback_above_of_isLimit D c hc j
    ((pullback (t.app j)).obj M) ((pullback (t.app j)).obj N) g
  have : IsIso ((pullback (D.map r)).map g) := hr
  have hrt : D.map r ≫ t.app j = t.app k :=
    (t.naturality r).trans (Category.comp_id _)
  let g' := pullbackHomOfTriangle (D.map r) (t.app j) (t.app k) hrt g
  have : IsIso g' := by
    dsimp only [g', pullbackHomOfTriangle]
    infer_instance
  let E := asIso g'
  have hE : pullbackHomOfTriangle (c.π.app k) (t.app k) l (hl k) E.hom = e.hom := by
    change pullbackHomOfTriangle (c.π.app k) (t.app k) l (hl k) g' = e.hom
    calc
      _ = pullbackHomOfTriangle (c.π.app k ≫ D.map r) (t.app j) l
          (by rw [Category.assoc, hrt, hl k]) g :=
        pullbackHomOfTriangle_comp (D.map r) (c.π.app k) (t.app j)
          (t.app k) hrt l (hl k) g
      _ = pullbackHomOfTriangle (c.π.app j) (t.app j) l (hl j) g := by
        congr 1
        exact c.w r
      _ = _ := hg
  exact ⟨k, r ≫ q, E, hE,
    pullbackHomOfTriangle_inv_eq (c.π.app k) (t.app k) l (hl k) E e hE⟩

private theorem pullbackConeCompIso_eq_symm {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {i j : I} (q : j ⟶ i) :
    pullbackConeCompIso D c q =
      (pullbackTriangleIso (c.π.app j) (D.map q) (c.π.app i) (c.w q)).symm := by
  rfl

/-- A given limit isomorphism between two original fp stage models descends
with both actual canonical cone-composition recovery equations. -/
theorem exists_iso_pullback_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (M N : (D.obj i).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (e : (pullback (c.π.app i)).obj M ≅ (pullback (c.π.app i)).obj N) :
    ∃ (j : I) (q : j ⟶ i)
      (e' : (pullback (D.map q)).obj M ≅ (pullback (D.map q)).obj N),
      (pullbackConeCompIso D c q).hom.app M ≫ (pullback (c.π.app j)).map e'.hom =
        e.hom ≫ (pullbackConeCompIso D c q).hom.app N ∧
      (pullbackConeCompIso D c q).hom.app N ≫ (pullback (c.π.app j)).map e'.inv =
        e.inv ≫ (pullbackConeCompIso D c q).hom.app M := by
  let D' := Over.forget i ⋙ D
  let c' : Cone D' :=
    { pt := c.pt
      π :=
        { app j := c.π.app j.left
          naturality {j k} q := c.π.naturality q.left } }
  have hc' : IsLimit c' :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have {j k : Over i} (q : j ⟶ k) : IsAffineHom (D'.map q) :=
    inferInstanceAs (IsAffineHom (D.map q.left))
  have (j : Over i) : CompactSpace (D'.obj j) := inferInstanceAs (CompactSpace (D.obj j.left))
  have (j : Over i) : QuasiSeparatedSpace (D'.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  let t : D' ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app j := D.map j.hom
      naturality {j k} q := by
        change D.map q.left ≫ D.map k.hom = D.map j.hom ≫ 𝟙 _
        rw [← D.map_comp, Over.w, Category.comp_id] }
  have hl (j : Over i) : c'.π.app j ≫ t.app j = c.π.app i := by
    change c.π.app j.left ≫ D.map j.hom = c.π.app i
    exact c.w j.hom
  obtain ⟨j, _, E, hE, hE'⟩ := exists_relative_iso_above_of_isLimit D' c' hc' t
    (c.π.app i) hl (Over.mk (𝟙 i)) M N e
  change pullbackHomOfTriangle (c.π.app j.left) (D.map j.hom) (c.π.app i)
    (c.w j.hom) E.hom = e.hom at hE
  change pullbackHomOfTriangle (c.π.app j.left) (D.map j.hom) (c.π.app i)
    (c.w j.hom) E.inv = e.inv at hE'
  refine ⟨j.left, j.hom, E, ?_, ?_⟩
  · let T := pullbackTriangleIso (c.π.app j.left) (D.map j.hom) (c.π.app i) (c.w j.hom)
    have hU : pullbackConeCompIso D c j.hom = T.symm := by
      exact pullbackConeCompIso_eq_symm D c j.hom
    rw [hU]
    change T.inv.app M ≫ (pullback (c.π.app j.left)).map E.hom = e.hom ≫ T.inv.app N
    apply (cancel_mono (T.hom.app N)).mp
    simpa only [T, pullbackHomOfTriangle, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id] using hE
  · let T := pullbackTriangleIso (c.π.app j.left) (D.map j.hom) (c.π.app i) (c.w j.hom)
    have hU : pullbackConeCompIso D c j.hom = T.symm := by
      exact pullbackConeCompIso_eq_symm D c j.hom
    rw [hU]
    change T.inv.app N ≫ (pullback (c.π.app j.left)).map E.inv = e.inv ≫ T.inv.app M
    apply (cancel_mono (T.hom.app M)).mp
    simpa only [T, pullbackHomOfTriangle, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id] using hE'

private theorem finitePresentation_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit X.ringCatSheaf :=
    CategoryTheory.Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} =>
      SheafOfModules.unit X.ringCatSheaf)
  exact (finitePresentation_iff_of_iso e).mp
    (finitePresentation_free (X := X) PUnit.{u + 1})

private theorem exists_affine_unit_frame {X : Scheme.{u}} (M : X.Modules)
    (hM : IsLocallyRankOne X M) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧
      Nonempty ((pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit M).mp hM x
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
  let r : V.toScheme ⟶ U.toScheme := X.homOfLE hVU
  have hr : r ≫ U.ι = V.ι := by
    simp only [r, Scheme.homOfLE_ι]
  refine ⟨V, hxV, hV, ⟨?_⟩⟩
  exact ((pullbackCongr hr).app M).symm ≪≫ ((pullbackComp r U.ι).app M).symm ≪≫
    (pullback r).mapIso (((restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e) ≪≫
    pullbackUnitIso r

private def openCoefficientStructure {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (i : I) (V : (D.obj i).Opens) :
    AlgebraicGeometry.opensDiagram D i V ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app j := (D.map j.hom ⁻¹ᵁ V).ι ≫ D.map j.hom
  naturality {j k} q := by
    change (D.map q.left).resLE _ _ _ ≫ ((D.map k.hom ⁻¹ᵁ V).ι ≫ D.map k.hom) =
      ((D.map j.hom ⁻¹ᵁ V).ι ≫ D.map j.hom) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Category.assoc, ← D.map_comp, Over.w q]

private def openLimitCoefficient {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) (V : (D.obj i).Opens) :
    (AlgebraicGeometry.opensCone D c i V).pt ⟶ D.obj i :=
  (c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i

private theorem openLimitCoefficient_w {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) (V : (D.obj i).Opens) (j : Over i) :
    (AlgebraicGeometry.opensCone D c i V).π.app j ≫ (openCoefficientStructure D i V).app j =
      openLimitCoefficient D c i V := by
  change (c.π.app j.left).resLE _ _ _ ≫ ((D.map j.hom ⁻¹ᵁ V).ι ≫ D.map j.hom) =
    (c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app i
  rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, c.w]

private theorem exists_rankOne_above_of_limit_frames
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (M : (D.obj i).Modules) [M.IsFinitePresentation]
    {A : Type u} [Finite A] (V : A → (D.obj i).Opens) (hV : IsOpenCover V)
    (hVa : ∀ a, IsAffineOpen (V a))
    (e : ∀ a, Nonempty ((pullback (c.π.app i ⁻¹ᵁ V a).ι).obj
      ((pullback (c.π.app i)).obj M) ≅
        SheafOfModules.unit (c.π.app i ⁻¹ᵁ V a).toScheme.ringCatSheaf)) :
    ∃ (j : I) (q : j ⟶ i), IsLocallyRankOne (D.obj j) ((pullback (D.map q)).obj M) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let O (a : A) := AlgebraicGeometry.opensDiagram D i (V a)
  have (a : A) (j : Over i) : IsAffine ((O a).obj j) :=
    (hVa a).preimage (D.map j.hom)
  have (a : A) (j : Over i) : CompactSpace ((O a).obj j) := inferInstance
  have (a : A) (j : Over i) : QuasiSeparatedSpace ((O a).obj j) := inferInstance
  let U := SheafOfModules.unit (D.obj i).ringCatSheaf
  let : U.IsFinitePresentation := finitePresentation_unit (D.obj i)
  let e₀ (a : A) : (pullback (openLimitCoefficient D c i (V a))).obj M ≅
      (pullback (openLimitCoefficient D c i (V a))).obj U :=
    ((pullbackComp (c.π.app i ⁻¹ᵁ V a).ι (c.π.app i)).app M).symm ≪≫
      (e a).some ≪≫ (pullbackUnitIso (openLimitCoefficient D c i (V a))).symm
  choose j q E hE hE' using fun a : A => exists_relative_iso_above_of_isLimit
    (O a) (AlgebraicGeometry.opensCone D c i (V a))
    (AlgebraicGeometry.isLimitOpensCone D c hc i (V a))
    (openCoefficientStructure D i (V a)) (openLimitCoefficient D c i (V a))
    (openLimitCoefficient_w D c i (V a)) (Over.mk (𝟙 i)) M U (e₀ a)
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let v (a : A) : k ⟶ j a := (hk (Finset.mem_image.mpr ⟨a, by simp, rfl⟩)).some
  let W (a : A) := D.map k.hom ⁻¹ᵁ V a
  let N := (pullback (D.map k.hom)).obj M
  let e' (a : A) :
      (pullback ((openCoefficientStructure D i (V a)).app k)).obj M ≅
        (pullback ((openCoefficientStructure D i (V a)).app k)).obj U := by
    let t := openCoefficientStructure D i (V a)
    have ht : (O a).map (v a) ≫ t.app (j a) = t.app k :=
      (t.naturality (v a)).trans (Category.comp_id _)
    let T := pullbackTriangleIso ((O a).map (v a)) (t.app (j a)) (t.app k) ht
    exact (T.app M).symm ≪≫ (pullback ((O a).map (v a))).mapIso (E a) ≪≫ T.app U
  let frame (a : A) : (pullback (W a).ι).obj N ≅
      SheafOfModules.unit (W a).toScheme.ringCatSheaf :=
    (pullbackComp (W a).ι (D.map k.hom)).app M ≪≫ e' a ≪≫
      pullbackUnitIso ((openCoefficientStructure D i (V a)).app k)
  have hW : IsOpenCover W := by
    apply IsOpenCover.mk
    apply top_le_iff.mp
    intro x _
    obtain ⟨a, ha⟩ := hV.exists_mem (D.map k.hom x)
    exact Opens.mem_iSup.mpr ⟨a, ha⟩
  refine ⟨k.left, k.hom, (isLocallyRankOne_iff_restrict_unit N).mpr ?_⟩
  intro x
  obtain ⟨a, ha⟩ := hW.exists_mem x
  exact ⟨W a, ha, ⟨(restrictFunctorIsoPullback (W a).ι).app N ≪≫ frame a⟩⟩

/-- Local rank one of the literal limit pullback of an original fp stage
module holds at a later literal pullback. The proof descends a genuine finite
affine trivializing cover and actual frame isomorphisms with their inverses. -/
theorem exists_isLocallyRankOne_pullback_above_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {j k} (q : j ⟶ k), IsAffineHom (D.map q)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    (M : (D.obj i).Modules) [M.IsFinitePresentation]
    (hM : IsLocallyRankOne c.pt ((pullback (c.π.app i)).obj M)) :
    ∃ (j : I) (q : j ⟶ i), IsLocallyRankOne (D.obj j) ((pullback (D.map q)).obj M) := by
  classical
  choose U hx hU e using fun x : c.pt =>
    exists_affine_unit_frame ((pullback (c.π.app i)).obj M) hM x
  have hcov : IsOpenCover U := .mk (by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩)
  obtain ⟨j, s, V, hV, hVa⟩ := Scheme.exists_isOpenCover_and_isAffine D c hc U hcov hU
  let k := IsCofiltered.min i j
  let qᵢ : k ⟶ i := IsCofiltered.minToLeft i j
  let qⱼ : k ⟶ j := IsCofiltered.minToRight i j
  let W (a : s) := D.map qⱼ ⁻¹ᵁ V a
  have hW : IsOpenCover W := by
    apply IsOpenCover.mk
    apply top_le_iff.mp
    intro x _
    obtain ⟨a, ha⟩ := hV.exists_mem (D.map qⱼ x)
    exact Opens.mem_iSup.mpr ⟨a, ha⟩
  have hWa (a : s) : IsAffineOpen (W a) := (hVa a).1.preimage (D.map qⱼ)
  have hUa (a : s) : U a.val = c.π.app k ⁻¹ᵁ W a := by
    dsimp only [W]
    rw [← Scheme.Hom.comp_preimage, c.w qⱼ]
    exact (hVa a).2
  let M' := (pullback (D.map qᵢ)).obj M
  have e' (a : s) : Nonempty ((pullback (c.π.app k ⁻¹ᵁ W a).ι).obj
      ((pullback (c.π.app k)).obj M') ≅
        SheafOfModules.unit (c.π.app k ⁻¹ᵁ W a).toScheme.ringCatSheaf) := by
    let A := c.π.app k ⁻¹ᵁ W a
    let Frame (B : c.pt.Opens) : Prop :=
      Nonempty ((pullback B.ι).obj ((pullback (c.π.app i)).obj M) ≅
        SheafOfModules.unit B.toScheme.ringCatSheaf)
    have eA : Frame A := (congrArg Frame (hUa a)).mp (e a.val)
    exact ⟨(pullback A.ι).mapIso ((pullbackConeCompIso D c qᵢ).app M).symm ≪≫ eA.some⟩
  obtain ⟨l, r, hr⟩ := exists_rankOne_above_of_limit_frames D c hc k M' W hW hWa e'
  let T : pullback (D.map (r ≫ qᵢ)) ≅ pullback (D.map qᵢ) ⋙ pullback (D.map r) :=
    pullbackCongr (D.map_comp r qᵢ) ≪≫ (pullbackComp (D.map r) (D.map qᵢ)).symm
  exact ⟨l, r ≫ qᵢ, isLocallyRankOne_of_iso _ (T.app M).symm hr⟩

end AlgebraicGeometry.Scheme.Modules
