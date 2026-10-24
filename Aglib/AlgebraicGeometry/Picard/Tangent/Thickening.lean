/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.Sheaf.SquareZeroSplitting
public import Aglib.Algebra.Group.Subgroup.KerEquiv
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Local
public import Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.KernelOpens
public import Mathlib.Topology.Sheaves.Functors

/-!
# Split square-zero thickenings: the unit sequence on the common space

Let `i : X ⟶ Y` and `p : Y ⟶ X` be morphisms of schemes with `i ≫ p = 𝟙 X`; the example is
`X ⟶ X[ε] ⟶ X` for the dual numbers. On the underlying space of `X`, the structure sheaf
of `Y` is the ring sheaf `ringSheaf p := p_* 𝒪_Y`; the map `reduction i p h` to `𝒪_X` comes
from `i^♯`, and `projectionMap p` from `p^♯` is a section of it. The unit-sequence results
assume square-zero section kernels of `reduction` on every open.

* `reduction_ker_sq`: these kernels are square-zero when `i` is quasi-compact with
  `i.ker ^ 2 = ⊥`, from the affine case and locality of sections.
* `unitsComplex_shortExact` and `unitsSplitting`: given square-zero section kernels
  (for example `reduction_ker_sq`), the original sequence
  `0 → I → (p_* 𝒪_Y)^* → 𝒪_X^* → 1` is short exact and split by `p^♯`.
* `unitsCohomologyEquiv`, `unitsCohomologyKerEquiv`: in every degree,
  `H^n((p_* 𝒪_Y)^*) ≃+ H^n(I) × H^n(𝒪_X^*)`, and the kernel of the original map to
  `H^n(𝒪_X^*)` is `H^n(I)`.
* `picardRetractionEquiv`: through the retraction, `Pic(Y) ≃+ Pic(X) × ker(i^*)`.
* `UnitsCohomologyComparison` and `picardKerEquiv`: given an equivalence of `Pic(Y)` and an
  injective map of `Pic(X)` with first unit cohomology on `|X|`, compatible with `i^*`, the
  kernel of `i^* : Pic(Y) → Pic(X)` is `H^1(I)`.

This is the sheaf-theoretic core of the tangent space of the Picard scheme
(Kleiman, arXiv:math/0504020v1, Thm 5.11). No quasi-compactness,
separatedness or Noetherian hypothesis on `X` is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

namespace AlgebraicGeometry.Scheme.SplitThickening

universe u

variable {X Y : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ X)

/-- The structure sheaf of `Y`, as a ring sheaf on the underlying space of `X`. -/
abbrev ringSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj Y.sheaf

theorem preimage_preimage_eq (h : i ≫ p = 𝟙 X) (U : X.Opens) : i ⁻¹ᵁ p ⁻¹ᵁ U = U := by
  change (i ≫ p) ⁻¹ᵁ U = U
  rw [h]
  rfl

/-- The closed-fibre map `p_* 𝒪_Y ⟶ 𝒪_X` induced by `i^♯`. -/
def reduction (h : i ≫ p = 𝟙 X) : ringSheaf p ⟶ X.sheaf :=
  ObjectProperty.homMk
  { app := fun U => i.app (p ⁻¹ᵁ U.unop) ≫
      X.presheaf.map (eqToHom (preimage_preimage_eq i p h U.unop).symm).op
    naturality := by
      intro U V g
      change Y.presheaf.map ((Opens.map p.base).map g.unop).op ≫ i.app (p ⁻¹ᵁ V.unop) ≫ _ =
        (i.app (p ⁻¹ᵁ U.unop) ≫ _) ≫ X.presheaf.map g
      rw [i.naturality_assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      rfl }

theorem reduction_app (h : i ≫ p = 𝟙 X) (U : X.Opensᵒᵖ) :
    (reduction i p h).hom.app U = i.app (p ⁻¹ᵁ U.unop) ≫
      X.presheaf.map (eqToHom (preimage_preimage_eq i p h U.unop).symm).op := rfl

/-- The map `𝒪_X ⟶ p_* 𝒪_Y` given by `p^♯`. -/
def projectionMap : X.sheaf ⟶ ringSheaf p :=
  ObjectProperty.homMk p.c

theorem projectionMap_app (U : X.Opensᵒᵖ) :
    (projectionMap p).hom.app U = p.app U.unop := rfl

/-- `p^♯` is a section of the closed-fibre map. -/
@[reassoc (attr := simp)]
theorem projectionMap_reduction (h : i ≫ p = 𝟙 X) :
    projectionMap p ≫ reduction i p h = 𝟙 X.sheaf := by
  apply Sheaf.hom_ext
  ext U : 2
  change p.app U.unop ≫ i.app (p ⁻¹ᵁ U.unop) ≫
    X.presheaf.map (eqToHom (preimage_preimage_eq i p h U.unop).symm).op = 𝟙 _
  rw [← Category.assoc, ← Scheme.Hom.comp_app, Scheme.Hom.congr_app h, Scheme.Hom.id_app,
    Category.id_comp, ← Functor.map_comp]
  simp
  rfl

/-- The section kernels of the closed-fibre map are square-zero on every open. -/
theorem reduction_ker_sq (h : i ≫ p = 𝟙 X) [QuasiCompact i] (hi : i.ker ^ 2 = ⊥)
    (U : X.Opensᵒᵖ) : RingHom.ker ((reduction i p h).hom.app U).hom ^ 2 = ⊥ := by
  have e : RingHom.ker ((reduction i p h).hom.app U).hom =
      RingHom.ker (i.app (p ⁻¹ᵁ U.unop)).hom := by
    change RingHom.ker ((X.presheaf.map
      (eqToHom (preimage_preimage_eq i p h U.unop).symm).op).hom.comp
        (i.app (p ⁻¹ᵁ U.unop)).hom) = _
    exact RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso _).injective
  rw [e]
  exact ker_app_sq_eq_bot i hi _

section Units

variable (h : i ≫ p = 𝟙 X)

/-- The original additive kernel sheaf `I` of the closed-fibre map, on `|X|`. -/
abbrev idealSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  Sheaf.additiveKernel.{u, u, u} (reduction i p h)

variable (hsq : ∀ U : X.Opensᵒᵖ, RingHom.ker ((reduction i p h).hom.app U).hom ^ 2 = ⊥)

/-- The original unit sequence `0 → I → (p_* 𝒪_Y)^* → 𝒪_X^* → 1` on `|X|`. -/
abbrev unitsComplex : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  Sheaf.squareZeroUnitsComplex.{u, u, u} (reduction i p h) hsq

/-- The one-plus map `I ⟶ (p_* 𝒪_Y)^*`. -/
abbrev oneAddUnits : idealSheaf i p h ⟶ (ringSheaf p).units :=
  Sheaf.oneAddUnits.{u, u, u} (reduction i p h) hsq

/-- The unit sequence of a split square-zero thickening is short exact. -/
theorem unitsComplex_shortExact : (unitsComplex i p h hsq).ShortExact :=
  haveI := Sheaf.isLocallySurjective_of_section.{u, u, u} (reduction i p h) (projectionMap p)
    (projectionMap_reduction i p h)
  Sheaf.squareZeroUnitsComplex_shortExact.{u, u, u} _ _

/-- The unit sequence is split by the units of `p^♯`. -/
def unitsSplitting : (unitsComplex i p h hsq).Splitting :=
  Sheaf.squareZeroUnitsSplitting.{u, u, u} (reduction i p h) (projectionMap p)
    (projectionMap_reduction i p h) hsq

/-- `H^n((p_* 𝒪_Y)^*) ≃+ H^n(I) × H^n(𝒪_X^*)`; the second component is the original map. -/
def unitsCohomologyEquiv (n : ℕ) :
    Sheaf.H (ringSheaf p).units n ≃+ Sheaf.H (idealSheaf i p h) n × Sheaf.H X.sheaf.units n :=
  Sheaf.squareZeroUnitsCohomologyEquiv.{u, u, u, u + 1} (reduction i p h) (projectionMap p)
    (projectionMap_reduction i p h) hsq n

@[simp]
theorem unitsCohomologyEquiv_apply_snd (n : ℕ) (x : Sheaf.H (ringSheaf p).units n) :
    (unitsCohomologyEquiv i p h hsq n x).2 =
      Sheaf.H.map (Sheaf.unitsMap (reduction i p h)) n x := rfl

@[simp]
theorem unitsCohomologyEquiv_symm_apply (n : ℕ)
    (y : Sheaf.H (idealSheaf i p h) n × Sheaf.H X.sheaf.units n) :
    (unitsCohomologyEquiv i p h hsq n).symm y =
      Sheaf.H.map (oneAddUnits i p h hsq) n y.1 +
        Sheaf.H.map (Sheaf.unitsMap (projectionMap p)) n y.2 := rfl

/-- The kernel of `H^n((p_* 𝒪_Y)^*) → H^n(𝒪_X^*)` is `H^n(I)`, through the one-plus map. -/
def unitsCohomologyKerEquiv (n : ℕ) :
    (Sheaf.H.map (Sheaf.unitsMap (reduction i p h)) n).ker ≃+ Sheaf.H (idealSheaf i p h) n :=
  Sheaf.squareZeroUnitsCohomologyKerEquiv.{u, u, u, u + 1} (reduction i p h) (projectionMap p)
    (projectionMap_reduction i p h) hsq n

@[simp]
theorem unitsCohomologyKerEquiv_symm_apply_coe (n : ℕ) (a : Sheaf.H (idealSheaf i p h) n) :
    (((unitsCohomologyKerEquiv i p h hsq n).symm a :
        (Sheaf.H.map (Sheaf.unitsMap (reduction i p h)) n).ker) :
          Sheaf.H (ringSheaf p).units n) =
      Sheaf.H.map (oneAddUnits i p h hsq) n a := rfl

end Units

section Picard

/-- Pullback along a retraction splits the Picard group of the thickening:
`Pic(Y) ≃+ Pic(X) × ker(i^*)`, `c ↦ (i^* c, c - p^* i^* c)`. -/
def picardRetractionEquiv (h : i ≫ p = 𝟙 X) :
    PicardGroup Y ≃+ PicardGroup X × (pullbackHom i).ker :=
  AddMonoidHom.retractionAddEquiv (pullbackHom i) (pullbackHom p) fun a => by
    rw [← AddMonoidHom.comp_apply, ← pullbackHom_comp, h, pullbackHom_id, AddMonoidHom.id_apply]

@[simp]
theorem picardRetractionEquiv_apply_fst (h : i ≫ p = 𝟙 X) (c : PicardGroup Y) :
    (picardRetractionEquiv i p h c).1 = pullbackHom i c := rfl

@[simp]
theorem picardRetractionEquiv_symm_apply (h : i ≫ p = 𝟙 X)
    (a : PicardGroup X × (pullbackHom i).ker) :
    (picardRetractionEquiv i p h).symm a = pullbackHom p a.1 + a.2.1 := rfl

/-- A comparison of the Picard groups of `Y` and `X` with first unit cohomology on the
common space `|X|`, compatible with the closed-fibre pullback: the Zariski form of
`Pic = H^1(𝒪^*)` (Stacks, Tag 09NU, `lemma-h1-invertible`) for `Y` and `X`, with `Y`
transported to `|X|`; `pullback_comm` is its naturality along `i`, which Tag 09NU does not
state. Kleiman uses this identification tacitly in the proof of Thm 5.11
(arXiv:math/0504020v1, p. 43, the sentence before Square (5.11.4)); the square itself compares
`H^1(𝒪^*_{X_T})` with `Pic_{X/k}(T)` and is not formalized here. For `X` only an injective
map is required. It is a premise here;
Aglib proves only the étale comparison `FrameTensor.picardH1Equiv`. -/
structure UnitsCohomologyComparison (h : i ≫ p = 𝟙 X) where
  /-- `Pic(Y) ≃+ H^1(|X|, (p_* 𝒪_Y)^*)`. -/
  thickening : PicardGroup Y ≃+ Sheaf.H (ringSheaf p).units 1
  /-- `Pic(X) →+ H^1(|X|, 𝒪_X^*)`; only its injectivity is used. -/
  base : PicardGroup X →+ Sheaf.H X.sheaf.units 1
  /-- The map for `X` is injective. -/
  base_injective : Function.Injective base
  /-- The comparison carries `i^*` to the original map on unit cohomology. -/
  pullback_comm : ∀ c : PicardGroup Y,
    base (pullbackHom i c) = Sheaf.H.map (Sheaf.unitsMap (reduction i p h)) 1 (thickening c)

variable {i p} in
/-- Under a unit-cohomology comparison, the kernel of `i^*` is the kernel of the original
map on unit cohomology. -/
def UnitsCohomologyComparison.kerEquiv {h : i ≫ p = 𝟙 X} (C : UnitsCohomologyComparison i p h) :
    (pullbackHom i).ker ≃+ (Sheaf.H.map (Sheaf.unitsMap (reduction i p h)) 1).ker :=
  AddMonoidHom.kerAddEquivOfComm _ _ C.thickening C.base C.base_injective C.pullback_comm

/-- Under a unit-cohomology comparison, `ker(i^* : Pic(Y) → Pic(X)) ≃+ H^1(I)`, where `I` is
the original additive kernel of the closed-fibre map. -/
def picardKerEquiv (h : i ≫ p = 𝟙 X)
    (hsq : ∀ U : X.Opensᵒᵖ, RingHom.ker ((reduction i p h).hom.app U).hom ^ 2 = ⊥)
    (C : UnitsCohomologyComparison i p h) :
    (pullbackHom i).ker ≃+ Sheaf.H (idealSheaf i p h) 1 :=
  C.kerEquiv.trans (unitsCohomologyKerEquiv i p h hsq 1)

/-- Under a unit-cohomology comparison, `Pic(Y) ≃+ Pic(X) × H^1(I)` through the retraction. -/
def picardEquiv (h : i ≫ p = 𝟙 X)
    (hsq : ∀ U : X.Opensᵒᵖ, RingHom.ker ((reduction i p h).hom.app U).hom ^ 2 = ⊥)
    (C : UnitsCohomologyComparison i p h) :
    PicardGroup Y ≃+ PicardGroup X × Sheaf.H (idealSheaf i p h) 1 :=
  (picardRetractionEquiv i p h).trans
    (AddEquiv.prodCongr (AddEquiv.refl _) (picardKerEquiv i p h hsq C))

end Picard

end AlgebraicGeometry.Scheme.SplitThickening
