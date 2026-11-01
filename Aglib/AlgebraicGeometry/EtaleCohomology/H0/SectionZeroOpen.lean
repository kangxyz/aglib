/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSectionZeroDetection
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsPullbackGerm
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FibrewiseClosed.Geometry

/-! # The original global section zero open and its pullback

The open is defined from the actual small-etale section. Its inverse image
under an arbitrary scheme morphism is exactly the zero open of the original
global-section pullback. Its being the whole scheme detects zero, by actual
etale sheaf separation. These are coefficient-independent inputs to descent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- The actual etale-local zero open of an original global section. -/
def sectionZeroOpen {X : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X)
    (a : (globalSections X).obj F) : X.Opens :=
  ⟨Scheme.Etale.sectionZeroLocus F.obj a, Scheme.Etale.isOpen_sectionZeroLocus F.obj a⟩

/-- A section vanishes if and only if its original zero open is the whole scheme. -/
theorem sectionZeroOpen_eq_top_iff {X : Scheme.{u}}
    (F : AbelianSheaf.{u, u + 1} X) (a : (globalSections X).obj F) :
    sectionZeroOpen F a = ⊤ ↔ a = 0 := by
  constructor
  · intro ha
    have h (x : X) : ∃ (V : X.Etale) (f : V ⟶ etaleTerminal X) (y : V.left),
        f.left y = x ∧ F.obj.map f.op a = 0 := by
      have hx : x ∈ sectionZeroOpen F a := by rw [ha]; trivial
      exact hx
    choose V f y hy hz using h
    have hc : Sieve.ofArrows V f ∈ X.smallEtaleTopology (etaleTerminal X) := by
      rw [ofArrows_mem_smallEtaleTopology_iff]
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨x, y x, hy x⟩
    apply F.isSeparated (etaleTerminal X) _ hc a 0
    intro W g hg
    obtain ⟨x, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hz,
      map_zero]
  · rintro rfl
    ext x
    constructor
    · intro _; trivial
    · intro _
      exact ⟨etaleTerminal X, 𝟙 _, x, rfl, map_zero _⟩

/-- The zero open commutes with the literal global-section pullback along any
scheme morphism, with no flatness or coefficient finiteness condition. -/
theorem sectionZeroOpen_globalSectionsPullback {X S : Scheme.{u}}
    (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    (a : (globalSections X).obj F) :
    sectionZeroOpen ((inverseImage f).obj F) (globalSectionsPullback f F a) =
      f ⁻¹ᵁ sectionZeroOpen F a := by
  ext x
  let η := FibrewiseClosed.geometricPoint x
  let p : (pointSmallEtale (η ≫ f)).fiber.obj (etaleTerminal X) :=
    Over.homMk (η ≫ f) (by simp)
  let p' : (pointSmallEtale η).fiber.obj (etaleTerminal S) :=
    Over.homMk η (by simp)
  have hp' : p'.left (default : Spec (.of (FibrewiseClosed.pointField x))) = x :=
    FibrewiseClosed.geometricPoint_apply x _
  have hp : p.left (default : Spec (.of (FibrewiseClosed.pointField x))) = f x := by
    change f (η default) = f x
    rw [FibrewiseClosed.geometricPoint_apply]
  have h₁ := Scheme.Etale.mem_sectionZeroLocus_iff_geometricGerm_eq_zero η
    ((inverseImage f).obj F).obj (globalSectionsPullback f F a) p'
  have h₂ := Scheme.Etale.mem_sectionZeroLocus_iff_geometricGerm_eq_zero (η ≫ f)
    F.obj a p
  rw [hp'] at h₁
  rw [hp] at h₂
  let e := (StalkInverseImage.stalkUnitNatIso f η).app F
  have he : e.hom ((pointSmallEtale (η ≫ f)).toPresheafFiber
      (etaleTerminal X) p F.obj a) =
        (pointSmallEtale η).toPresheafFiber (etaleTerminal S) p'
          ((inverseImage f).obj F).obj (globalSectionsPullback f F a) :=
    ConcreteCategory.congr_hom (globalSectionsPullback_germ f η F p p') a
  have hz : (pointSmallEtale η).toPresheafFiber (etaleTerminal S) p'
        ((inverseImage f).obj F).obj (globalSectionsPullback f F a) = 0 ↔
      (pointSmallEtale (η ≫ f)).toPresheafFiber (etaleTerminal X) p F.obj a = 0 := by
    constructor
    · intro h
      exact (ConcreteCategory.bijective_of_isIso e.hom).injective
        ((he.trans h).trans (map_zero e.hom.hom).symm)
    · intro h
      exact he.symm.trans (by rw [h, map_zero])
  exact h₁.trans (hz.trans h₂.symm)

/-- An actual coefficient isomorphism leaves the original zero open unchanged. -/
theorem sectionZeroOpen_mapIso {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X} (e : F ≅ G)
    (a : (globalSections X).obj F) :
    sectionZeroOpen G ((globalSections X).map e.hom a) = sectionZeroOpen F a := by
  ext x
  change x ∈ Scheme.Etale.sectionZeroLocus G.obj (e.hom.hom.app _ a) ↔
    x ∈ Scheme.Etale.sectionZeroLocus F.obj a
  constructor
  · rintro ⟨V, f, y, hy, hz⟩
    refine ⟨V, f, y, hy, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op V))).injective
    have hn := ConcreteCategory.congr_hom (e.hom.hom.naturality f.op) a
    exact hn.trans (hz.trans (map_zero _).symm)
  · rintro ⟨V, f, y, hy, hz⟩
    refine ⟨V, f, y, hy, ?_⟩
    have hn := ConcreteCategory.congr_hom (e.hom.hom.naturality f.op) a
    exact hn.symm.trans ((congrArg (e.hom.hom.app (op V)) hz).trans (map_zero _))

end AlgebraicGeometry.Scheme.EtaleCohomology
