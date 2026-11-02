/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.UniversallyOpenAmalgamation
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedTorsionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.SepClosedConstant
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Original connected pullback sections over geometric fields

The coefficient over a geometric field is the actual original inverse image.
Its native constant-adjunction counit identifies it with its actual torsion
section group. Connected qcqs section pullback then supplies the original
map, rather than a finite-locally-constant replacement. This is the geometric
fibre input to arbitrary bounded-coefficient matching and open descent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

open Continuity
attribute [local instance] hasSheafifyLarge

/-- Original section pullback from a separably closed field to a connected
qcqs scheme is invertible for every coefficient with torsion sections. -/
theorem globalSectionsPullback_isIso_of_sepClosed_connected
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    {Y : Scheme.{u}} [ConnectedSpace Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (p : Y ⟶ Spec (.of Ω))
    (G : AbelianSheaf.{u, u + 1} (Spec (.of Ω)))
    (hG : IsAddTorsion ((globalSections (Spec (.of Ω))).obj G)) :
    IsIso (globalSectionsPullback p G) :=
  globalSectionsPullback_isIso_of_torsionConstantIso p
    ((globalSections (Spec (.of Ω))).obj G) hG G
    (fieldTorsionConstantIso Ω G hG)

/-- The same statement for the existing relative-section functor retains the
original commuting-triangle coefficient isomorphism. -/
theorem pullbackSectionsMap_isIso_to_sepClosed_connected
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X)
    {Y : Over X} [ConnectedSpace Y.left] [CompactSpace Y.left]
    [QuasiSeparatedSpace Y.left] (a : Y ⟶ Over.mk η)
    (hF : IsAddTorsion ((globalSections (Spec (.of Ω))).obj ((inverseImage η).obj F))) :
    IsIso ((pullbackSectionsFunctor F).map a.op) := by
  let : IsIso (globalSectionsPullback a.left ((inverseImage η).obj F)) :=
    globalSectionsPullback_isIso_of_sepClosed_connected Ω a.left ((inverseImage η).obj F) hF
  change IsIso (globalSectionsPullback a.left ((inverseImage η).obj F) ≫
    (globalSections Y.left).map
      ((pullbackTriangleIso Y.hom η a.left (Over.w a)).inv.app F))
  infer_instance

/-- The original fibre counit and its two original lifts compare sections
inside one supplied functor. The fibre and all arrows are the existing over
category pullback construction. -/
private theorem relativeSection_eq_of_fibre_map_isIso
    {X : Scheme.{u}} (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1}) (T V : Over X)
    [IsIso (P.map ((Over.mapPullbackAdj T.hom).counit.app V).op)]
    (s : P.obj (op T)) (a b : V ⟶ T) : P.map a.op s = P.map b.op s := by
  let Q := (Over.map T.hom).obj ((Over.pullback T.hom).obj V)
  let q : Q ⟶ V := (Over.mapPullbackAdj T.hom).counit.app V
  let d : Q ⟶ T := Over.homMk (pullback.snd V.hom T.hom)
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso (P.map q.op)).surjective
    (P.map d.op s)
  have hc (c : V ⟶ T) : P.map c.op s = w := by
    let r : V ⟶ Q := Over.homMk
      (pullback.lift (𝟙 V.left) c.left
        ((Category.id_comp V.hom).trans (Over.w c).symm))
      (by
        change (pullback.lift (𝟙 V.left) c.left _) ≫
          (pullback.snd V.hom T.hom ≫ T.hom) = V.hom
        rw [← Category.assoc, pullback.lift_snd]
        exact Over.w c)
    have hd : r ≫ d = c := by
      apply Over.OverMorphism.ext
      exact pullback.lift_snd _ _ _
    have hq : r ≫ q = 𝟙 V := by
      apply Over.OverMorphism.ext
      exact pullback.lift_fst _ _ _
    calc
      P.map c.op s = P.map r.op (P.map d.op s) := by
        rw [← hd]
        simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      _ = P.map r.op (P.map q.op w) := congrArg _ hw.symm
      _ = w := by
        have hm := ConcreteCategory.congr_hom (P.map_comp q.op r.op) w
        have hid := P.map_id (op V)
        simpa only [← op_comp, hq, op_id, hid, ConcreteCategory.id_apply,
          ConcreteCategory.comp_apply] using hm.symm
  exact (hc a).trans (hc b).symm

/-- Two original geometric-point lifts into a qcqs geometrically connected
relative scheme give the same restriction of every section whose coefficient
at that geometric base point has torsion sections. The comparison uses the
literal fibre product and its original sections. -/
theorem relative_section_eq_at_geometric_lifts
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) (T : Over X)
    [QuasiCompact T.hom] [QuasiSeparated T.hom] [GeometricallyConnected T.hom]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X)
    (hF : IsAddTorsion ((globalSections (Spec (.of Ω))).obj ((inverseImage η).obj F)))
    (s : (pullbackSectionsFunctor F).obj (op T))
    (a b : Over.mk η ⟶ T) :
    (pullbackSectionsFunctor F).map a.op s =
      (pullbackSectionsFunctor F).map b.op s := by
  let V := Over.mk η
  let Q := (Over.map T.hom).obj ((Over.pullback T.hom).obj V)
  let q : Q ⟶ V := (Over.mapPullbackAdj T.hom).counit.app V
  let : ConnectedSpace Q.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := pullback.fst η T.hom)
  let : CompactSpace Q.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst η T.hom)
  let : QuasiSeparatedSpace Q.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst η T.hom)
  let : IsIso ((pullbackSectionsFunctor F).map q.op) :=
    pullbackSectionsMap_isIso_to_sepClosed_connected F Ω η q hF
  exact relativeSection_eq_of_fibre_map_isIso (pullbackSectionsFunctor F) T V s a b

/-- A genuine nonzero annihilator gives torsion in the actual field section
group by the original additive functors. No finiteness of that group is used. -/
theorem isAddTorsion_field_sections_of_killed
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0)
    (Ω : Type u) [Field Ω] (η : Spec (.of Ω) ⟶ X) :
    IsAddTorsion ((globalSections (Spec (.of Ω))).obj ((inverseImage η).obj F)) := by
  let H := inverseImage η ⋙ globalSections (Spec (.of Ω))
  intro x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  have h := congrArg (fun a : F ⟶ F => H.map a) hF
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at h
  have hx := congrArg (fun a : H.obj F ⟶ H.obj F => a x) h
  simpa using hx

/-- Complete detection of relative matching from the original geometric
point lifts. The zero-open constructor and all restrictions belong to the
same supplied section functor; no coefficient realization is changed. -/
private theorem matching_of_geometric_lifts
    {X : Scheme.{u}} (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1})
    (Z : ∀ R : Over X, P.obj (op R) → R.left.Opens)
    (hZ : ∀ {R U : Over X} (a : R ⟶ U) (t : P.obj (op U)),
      Z R (P.map a.op t) = a.left ⁻¹ᵁ Z U t)
    (hzero : ∀ (R : Over X) (t : P.obj (op R)), Z R t = ⊤ ↔ t = 0)
    (T : Over X) (s : P.obj (op T))
    (hiso : ∀ (R : Over X) (x : R.left),
      IsIso (P.map ((Over.mapPullbackAdj T.hom).counit.app
        (Over.mk (FibrewiseClosed.geometricPoint x ≫ R.hom))).op)) :
    ∀ (R : Over X) (a b : R ⟶ T), P.map a.op s = P.map b.op s := by
  intro R a b
  apply sub_eq_zero.mp
  apply (hzero R _).mp
  ext x
  constructor
  · intro _; trivial
  · intro _
    let Ω := FibrewiseClosed.pointField x
    let η := FibrewiseClosed.geometricPoint x
    let V : Over X := Over.mk (η ≫ R.hom)
    let r : V ⟶ R := Over.homMk η
    let := hiso R x
    have he := relativeSection_eq_of_fibre_map_isIso P T V s (r ≫ a) (r ≫ b)
    let δ := P.map a.op s -
      P.map b.op s
    have hz : P.map r.op δ = 0 := by
      have ha := (ConcreteCategory.congr_hom
        (P.map_comp a.op r.op) s).symm
      have hb := (ConcreteCategory.congr_hom
        (P.map_comp b.op r.op) s).symm
      exact (map_sub (P.map r.op).hom _ _).trans
        ((congrArg₂ (fun x y : P.obj (op V) => x - y)
          ha hb).trans (sub_eq_zero.mpr he))
    have htop : Z V
        (P.map r.op δ) = ⊤ :=
      (hzero V _).mpr hz
    rw [hZ] at htop
    have hy : (default : Spec (.of Ω)) ∈ r.left ⁻¹ᵁ Z R δ := by
      rw [htop]; trivial
    change η (default : Spec (.of Ω)) ∈ Z R δ at hy
    rw [FibrewiseClosed.geometricPoint_apply] at hy
    exact hy

/-- Bounded coefficients give equal restrictions at the two lifts of the
same original geometric point. This producer retains the actual point field
and its original map, rather than an abstract replacement field. -/
abbrev relativeSectionEqAtPointLiftsOfKilled
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) (T : Over X)
    [QuasiCompact T.hom] [QuasiSeparated T.hom] [GeometricallyConnected T.hom]
    (s : (pullbackSectionsFunctor F).obj (op T)) (R : Over X) (x : R.left)
    (a b : Over.mk (FibrewiseClosed.geometricPoint x ≫ R.hom) ⟶ T) :=
  relative_section_eq_at_geometric_lifts F T
    (FibrewiseClosed.pointField x) (FibrewiseClosed.geometricPoint x ≫ R.hom)
    (isAddTorsion_field_sections_of_killed F n hn hF
      (FibrewiseClosed.pointField x) (FibrewiseClosed.geometricPoint x ≫ R.hom)) s a b

/-- The actual geometric fibre counit is invertible on the original relative
sections of a bounded coefficient. This supplies a map law, not a second
construction of elementwise lift comparisons. -/
private theorem fibreSectionsMap_isIso_at_point_of_killed
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) (T : Over X)
    [QuasiCompact T.hom] [QuasiSeparated T.hom] [GeometricallyConnected T.hom]
    (R : Over X) (x : R.left) :
    IsIso ((pullbackSectionsFunctor F).map
      ((Over.mapPullbackAdj T.hom).counit.app
        (Over.mk (FibrewiseClosed.geometricPoint x ≫ R.hom))).op) := by
  let η := FibrewiseClosed.geometricPoint x ≫ R.hom
  let V := Over.mk η
  let Q := (Over.map T.hom).obj ((Over.pullback T.hom).obj V)
  let q : Q ⟶ V := (Over.mapPullbackAdj T.hom).counit.app V
  let : ConnectedSpace Q.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := pullback.fst η T.hom)
  let : CompactSpace Q.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst η T.hom)
  let : QuasiSeparatedSpace Q.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst η T.hom)
  exact pullbackSectionsMap_isIso_to_sepClosed_connected F
    (FibrewiseClosed.pointField x) η q
    (isAddTorsion_field_sections_of_killed F n hn hF (FibrewiseClosed.pointField x) η)

/-- Every original section of the pullback of a bounded coefficient matches
on the original relative arrows of a qcqs geometrically connected morphism.
Geometric points are used only through the original zero-open pullback law. -/
theorem isMatchingRelativeSection_of_geometricallyConnected
    {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) (T : Over X)
    [QuasiCompact T.hom] [QuasiSeparated T.hom] [GeometricallyConnected T.hom]
    (s : (pullbackSectionsFunctor F).obj (op T)) :
    IsMatchingRelativeSection F T s := by
  exact matching_of_geometric_lifts (pullbackSectionsFunctor F)
    (relativeSectionZeroOpen F) (fun a t => relativeSectionZeroOpen_map F a t)
    (relativeSectionZeroOpen_top_iff F) T s
    (fibreSectionsMap_isIso_at_point_of_killed F n hn hF T)

/-- Original global-section pullback is bijective for every n-killed sheaf
under a universally open qcqs geometrically connected morphism. This is not a
finite-locally-constant or quasicoherent coefficient assertion. -/
theorem globalSectionsPullback_bijective_of_geometricallyConnected
    {X S : Scheme.{u}} (f : S ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [GeometricallyConnected f] [UniversallyOpen f]
    (F : AbelianSheaf.{u, u + 1} X) (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0) :
    Function.Bijective (globalSectionsPullback f F) := by
  let : QuasiCompact (Over.mk f).hom := inferInstanceAs (QuasiCompact f)
  let : QuasiSeparated (Over.mk f).hom := inferInstanceAs (QuasiSeparated f)
  let : GeometricallyConnected (Over.mk f).hom := inferInstanceAs (GeometricallyConnected f)
  constructor
  · intro s t h
    let e := pullbackSectionsEtaleEvaluationIso F (etaleTerminal X)
    let q : Over.mk f ⟶ Over.mk (𝟙 X) := Over.homMk f (by simp)
    let : Surjective q.left := inferInstanceAs (Surjective f)
    apply (ConcreteCategory.bijective_of_isIso e.inv).injective
    apply pullbackSectionsMap_injective_of_surjective F q
    have hs := ConcreteCategory.congr_hom (terminalRelativeSectionPullback_eq f F) s
    have ht := ConcreteCategory.congr_hom (terminalRelativeSectionPullback_eq f F) t
    exact hs.trans (h.trans ht.symm)
  · intro s
    obtain ⟨t, ht, _⟩ := existsUnique_globalSection_of_universallyOpen_surjective f F s
      (isMatchingRelativeSection_of_geometricallyConnected F n hn hF (Over.mk f) s)
    exact ⟨t, ht⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
