/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.SectionZeroOpen
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.BaseChangeSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleDirectImageMate

/-! # Whole-fibre zero neighborhoods under a closed map

The complement of the closed image of the nonzero locus supplies an actual
open neighborhood downstairs. Every point of the fibre is required. The
original etale exchange and global-section comparison transport zero; no
cover descent, finite hypothesis or direct-image zero reflection is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u
attribute [local instance] hasSheafifyLarge

/-- Original sections correspond over an etale target chart, including their
vanishing. This is the actual exchange map, not a new section model. -/
theorem directImage_section_pullback_eq_zero_iff {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) [Etale g]
    (F : AbelianSheaf.{u, u + 1} X)
    (a : (globalSections S).obj ((directImage f).obj F)) :
    globalSectionsPullback g ((directImage f).obj F) a = 0 ↔
      globalSectionsPullback (pullback.snd g f) F
        ((directImageGlobalSectionsIso f).hom.app F a) = 0 := by
  let e := (globalSections T).mapIso ((etaleBaseChangeIso f g).app F) ≪≫
    (directImageGlobalSectionsIso (pullback.fst g f)).app
      ((inverseImage (pullback.snd g f)).obj F)
  have he : e.hom (globalSectionsPullback g ((directImage f).obj F) a) =
      globalSectionsPullback (pullback.snd g f) F
        ((directImageGlobalSectionsIso f).hom.app F a) := by
    have h := ConcreteCategory.congr_hom
      (baseChangeMap_globalSections f (pullback.fst g f) g
        (pullback.snd g f) pullback.condition F) a
    rw [← etaleBaseChangeIso_hom] at h
    exact h
  constructor
  · intro h
    exact he.symm.trans ((congrArg e.hom h).trans (map_zero _))
  · intro h
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    exact (he.trans h).trans (map_zero _).symm

/-- A closed map transports simultaneous local vanishing at every point of
one fibre to a whole target open. Both conclusions concern the original
section, under the canonical direct-image and cartesian comparisons. -/
theorem exists_closedMap_section_zero_neighborhood {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : IsClosedMap f)
    (F : AbelianSheaf.{u, u + 1} X)
    (a : (globalSections S).obj ((directImage f).obj F)) (x : S)
    (hx : ∀ y : X, f y = x →
      y ∈ sectionZeroOpen F ((directImageGlobalSectionsIso f).hom.app F a)) :
    ∃ U : S.Opens, x ∈ U ∧
      globalSectionsPullback (pullback.snd U.ι f) F
        ((directImageGlobalSectionsIso f).hom.app F a) = 0 ∧
      globalSectionsPullback U.ι ((directImage f).obj F) a = 0 := by
  let V := sectionZeroOpen F ((directImageGlobalSectionsIso f).hom.app F a)
  let U : S.Opens := ⟨(f '' (V : Set X)ᶜ)ᶜ, (hf _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have hxU : x ∈ U := by
    rintro ⟨y, hy, hyx⟩
    exact hy (hx y hyx)
  have hz : globalSectionsPullback (pullback.snd U.ι f) F
      ((directImageGlobalSectionsIso f).hom.app F a) = 0 := by
    apply (sectionZeroOpen_eq_top_iff _ _).mp
    rw [sectionZeroOpen_globalSectionsPullback]
    apply top_unique
    intro y _
    change pullback.snd U.ι f y ∈ V
    by_contra hy
    have he := congrArg (fun k : pullback U.ι f ⟶ S => k y)
      (pullback.condition (f := U.ι) (g := f))
    change U.ι (pullback.fst U.ι f y) = f (pullback.snd U.ι f y) at he
    exact (pullback.fst U.ι f y).property
      ⟨pullback.snd U.ι f y, hy, he.symm⟩
  exact ⟨U, hxU, hz, (directImage_section_pullback_eq_zero_iff f U.ι F a).mpr hz⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
