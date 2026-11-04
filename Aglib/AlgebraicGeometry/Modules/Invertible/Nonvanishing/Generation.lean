/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Generators.GlobalSections
public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Nonzero
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Trivialization
public import Aglib.AlgebraicGeometry.Modules.Locality.Epimorphisms
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitSectionMaps

/-! The actual global evaluation and the nonvanishing cover of a line bundle. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X Y : Scheme.{u}}

private theorem pulled_section_map (a : Y ⟶ X) {L : LineBundle X} (s : Γ(L.val, ⊤)) :
    (pullbackUnitIso a).inv ≫
        (Scheme.Modules.pullback a).map ((unitHomGlobalSectionsEquiv X L.val).symm s) =
      (unitHomGlobalSectionsEquiv Y ((Scheme.Modules.pullback a).obj L.val)).symm
        (Nonvanishing.pullbackSection a L.val s) := by
  apply (unitHomGlobalSectionsEquiv Y ((Scheme.Modules.pullback a).obj L.val)).injective
  rw [Equiv.apply_symm_apply]
  exact unitHomGlobalSectionsEquiv_pullbackUnitIso_inv_comp a s

/-- A covering by nonvanishing opens makes the actual all-sections
evaluation epimorphic. -/
theorem epi_globalSectionsEval_of_nonvanishing_cover (L : LineBundle X)
    (hL : ∀ x : X, ∃ s : Γ(L.val, ⊤), x ∈ nonvanishingOpen L s) :
    Epi (globalSectionsEval L.val) := by
  let V (s : Γ(L.val, ⊤)) := nonvanishingOpen L s
  refine epi_of_pullback_openCover (fun s => (V s).toScheme) (fun s => (V s).ι) ?_
    (globalSectionsEval L.val) ?_
  · intro x
    obtain ⟨s, hx⟩ := hL x
    exact ⟨s, ⟨x, hx⟩, rfl⟩
  · intro s
    let a := (V s).ι
    let F := Scheme.Modules.pullback a
    let i := Sigma.ι (fun _ : 𝟙_ X.Modules ⟶ L.val => 𝟙_ X.Modules)
      ((unitHomGlobalSectionsEquiv X L.val).symm s)
    have hs : nonvanishingOpen (pullbackLineBundle a L)
        (Nonvanishing.pullbackSection a L.val s) = ⊤ := by
      rw [Nonvanishing.nonvanishingOpen_pullback]
      ext x
      exact ⟨fun _ => trivial, fun _ => x.property⟩
    let f := (unitHomGlobalSectionsEquiv X L.val).symm s
    let g := (unitHomGlobalSectionsEquiv (V s).toScheme (F.obj L.val)).symm
      (Nonvanishing.pullbackSection a L.val s)
    have hg : IsIso g := Nonvanishing.section_isIso_of_nonvanishingOpen_eq_top
      (pullbackLineBundle a L) (Nonvanishing.pullbackSection a L.val s) hs
    have hi : i ≫ globalSectionsEval L.val = f := ι_globalSectionsEval L.val f
    have h := (F.map_comp i (globalSectionsEval L.val)).symm.trans (congrArg F.map hi)
    have hg' : Epi g := @IsIso.epi_of_iso _ _ _ _ g hg
    have hcomp : ((pullbackUnitIso a).inv ≫ F.map i) ≫ F.map (globalSectionsEval L.val) = g :=
      (Category.assoc _ _ _).trans ((congrArg ((pullbackUnitIso a).inv ≫ ·) h).trans
        (pulled_section_map a (L := L) s))
    exact @epi_of_epi_fac _ _ _ _ _ _ _ g hg' hcomp

/-- If the actual evaluation is epimorphic, some original section is
nonvanishing at each point, detected over its actual residue field. -/
theorem nonvanishing_cover_of_epi_globalSectionsEval (L : LineBundle X)
    [Epi (globalSectionsEval L.val)] (x : X) :
    ∃ s : Γ(L.val, ⊤), x ∈ nonvanishingOpen L s := by
  classical
  by_contra! h
  let K := X.residueField x
  let Y := Spec K
  let a : Y ⟶ X := X.fromSpecResidueField x
  let F := Scheme.Modules.pullback a
  let N := pullbackLineBundle a L
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let U : F.obj (𝟙_ X.Modules) ≅ O := pullbackUnitIso a
  let v := globalSectionsEval L.val
  let I := (𝟙_ X.Modules ⟶ L.val)
  let A (_ : I) := 𝟙_ X.Modules
  have hz (s : I) : F.map s = 0 := by
    let t := unitHomGlobalSectionsEquiv X L.val s
    have ht : nonvanishingOpen N (Nonvanishing.pullbackSection a L.val t) = ⊥ := by
      rw [Nonvanishing.nonvanishingOpen_pullback]
      ext y
      change a y ∈ nonvanishingOpen L t ↔ False
      rw [Scheme.fromSpecResidueField_apply]
      exact iff_false_intro (h t)
    have ht0 := eq_zero_of_nonvanishingOpen_eq_bot N _ ht
    have ht1 : (unitHomGlobalSectionsEquiv X L.val).symm t = s :=
      (unitHomGlobalSectionsEquiv X L.val).symm_apply_apply s
    let e : (O ⟶ F.obj L.val) ≃+ Γ(F.obj L.val, ⊤) :=
      unitHomGlobalSectionsAddEquiv Y (F.obj L.val)
    have hp0 : U.inv ≫ F.map s = (0 : O ⟶ F.obj L.val) :=
      (congrArg (fun z => U.inv ≫ F.map z) ht1.symm).trans
        ((pulled_section_map a (L := L) t).trans ((congrArg e.symm ht0).trans e.symm.map_zero))
    exact (cancel_epi U.inv).mp (hp0.trans (comp_zero (f := U.inv)).symm)
  have hv : F.map v = 0 := by
    let H := isColimitOfPreserves F (coproductIsCoproduct A)
    apply H.hom_ext
    intro s
    let i := Sigma.ι A s.as
    have hi : i ≫ v = s.as := ι_globalSectionsEval L.val s.as
    change F.map i ≫ F.map v = F.map i ≫ 0
    calc
      _ = F.map (i ≫ v) := (F.map_comp i v).symm
      _ = F.map s.as := congrArg F.map hi
      _ = 0 := hz s.as
      _ = _ := (comp_zero (f := F.map i)).symm
  let : Epi v := inferInstanceAs (Epi (globalSectionsEval L.val))
  let : F.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_adjunction
    (pullbackPushforwardAdjunction a)
  let : Epi (F.map v) := F.map_epi v
  have hN : 𝟙 N.val = 0 := (cancel_epi (F.map v)).mp
    ((Category.comp_id _).trans (hv.trans (comp_zero (f := F.map v)).symm))
  obtain ⟨e⟩ := nonempty_iso_unit_of_isLocalRing K N
  have hO : 𝟙 O = 0 := by
    calc
      𝟙 _ = e.inv ≫ e.hom := e.inv_hom_id.symm
      _ = e.inv ≫ (𝟙 N.val) ≫ e.hom := by rw [Category.id_comp]
      _ = 0 := by rw [hN, zero_comp, comp_zero]
  have h10 : (1 : Γ(Y, ⊤)) = 0 := by
    change Scheme.Modules.Hom.app (𝟙 O) ⊤
      (1 : Γ(Y, ⊤)) = 0
    rw [hO]
    rfl
  have he := congrArg (Scheme.ΓSpecIso K).hom.hom h10
  rw [map_one, map_zero] at he
  exact (one_ne_zero : (1 : K) ≠ 0) he

end AlgebraicGeometry.Scheme.Modules.Invertible
