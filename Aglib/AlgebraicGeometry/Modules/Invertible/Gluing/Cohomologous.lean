/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.ChartCocycle

/-!
# Cohomologous unit cocycles and isomorphic glued line bundles

Let `c` and `c'` be unit cocycles on the same open cover `U` of a scheme `X`. They are
cohomologous through units `u i ∈ Γ(X, U i)ˣ` (`UnitCocycle.Cohomologous c c' u`) if
`c'ᵢⱼ uⱼ = cᵢⱼ uᵢ` on every pairwise intersection.

* `UnitCocycle.sheafIsoOfCohomologous`: cohomologous cocycles glue to isomorphic module
  sheaves; the isomorphism sends the generator of chart `i` of `c` to `uᵢ` times the
  generator of chart `i` of `c'`.
* `UnitCocycle.exists_cohomologous_of_iso`: conversely, every isomorphism of the glued sheaves
  comes from such units, namely the coordinates of the images of the generators.
* `UnitCocycle.oneSheafIso`: the trivial cocycle `1` glues to the structure sheaf.
* `UnitCocycle.classOf_lineBundle_eq_iff`, `UnitCocycle.classOf_lineBundle_eq_zero_iff`: two
  glued line bundles have the same class in the Picard group if and only if their cocycles
  are cohomologous, and a glued line bundle is trivial if and only if its cocycle is
  cohomologous to `1`.
* `UnitCocycle.twist`: changing the frames of a cocycle by units gives a cohomologous cocycle.

This is the injectivity half of the classical description of line bundles trivialized on a
fixed cover by Čech 1-cocycles of `𝒪_X^*` modulo coboundaries (the torsor form is Stacks,
Tag 0B8R: Čech `H^1` of a covering classifies the torsors trivial on its members). No hypothesis
on `X` or on the cover is used beyond `iSup U = ⊤`.
-/

@[expose] public section

noncomputable section


open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- Module-sheaf morphisms are linear on sections, with the scalar written in `Γ(X, V)`. -/
theorem val_app_smul {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (V : X.Opens)
    (r : Γ(X, V)) (x : M.val.obj (op V)) : f.val.app (op V) (r • x) = r • f.val.app (op V) x :=
  (f.val.app (op V)).hom.map_smul r x

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}

/-- Unit cocycles with the same transition units are equal. -/
theorem ext {c c' : UnitCocycle U} (h : ∀ i j, c.transition i j = c'.transition i j) :
    c = c' := by
  obtain ⟨t, _⟩ := c
  obtain ⟨t', _⟩ := c'
  obtain rfl : t = t' := funext fun i => funext fun j => h i j
  rfl

/-- Restriction of units along two successive inclusions of opens. -/
theorem units_map_sectionRestrict_comp {V W T : X.Opens} (h : V ≤ W) (k : W ≤ T)
    (a : (Γ(X, T))ˣ) :
    Units.map (sectionRestrict X h).toMonoidHom
        (Units.map (sectionRestrict X k).toMonoidHom a) =
      Units.map (sectionRestrict X (h.trans k)).toMonoidHom a :=
  Units.ext (sectionRestrict_comp X h k a)

/-- On the pairwise intersection itself, `transitionOn` is the transition unit. -/
@[simp]
theorem transitionOn_inf (c : UnitCocycle U) (i j : ι) :
    c.transitionOn i j inf_le_left inf_le_right = c.transition i j :=
  Units.ext (sectionRestrict_refl X _ _)

/-- The trivial cocycle, with all transition units equal to one. -/
instance : One (UnitCocycle U) where
  one := ⟨fun _ _ => 1, fun _ _ _ _ _ _ _ => by simp only [map_one, mul_one]⟩

@[simp]
theorem one_transition (i j : ι) : (1 : UnitCocycle U).transition i j = 1 := rfl

@[simp]
theorem one_transitionOn (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) :
    (1 : UnitCocycle U).transitionOn i j hi hj = 1 :=
  map_one _

/-- `c'` is obtained from `c` by changing the frame of each chart `i` by the unit `u i`:
`c'ᵢⱼ uⱼ = cᵢⱼ uᵢ` on `U i ⊓ U j`. -/
def Cohomologous (c c' : UnitCocycle U) (u : ∀ i, (Γ(X, U i))ˣ) : Prop :=
  ∀ i j, c'.transition i j * Units.map (sectionRestrict X inf_le_right).toMonoidHom (u j) =
    c.transition i j * Units.map (sectionRestrict X inf_le_left).toMonoidHom (u i)

variable {c c' : UnitCocycle U} {u : ∀ i, (Γ(X, U i))ˣ}

/-- The cohomology relation after restriction to a common subopen. -/
theorem Cohomologous.transitionOn (h : Cohomologous c c' u) (i j : ι) {V : X.Opens}
    (hi : V ≤ U i) (hj : V ≤ U j) :
    (c'.transitionOn i j hi hj : Γ(X, V)) * sectionRestrict X hj (u j : Γ(X, U j)) =
      (c.transitionOn i j hi hj : Γ(X, V)) * sectionRestrict X hi (u i : Γ(X, U i)) := by
  have e : sectionRestrict X (le_inf hi hj) ((c'.transition i j : Γ(X, U i ⊓ U j)) *
      sectionRestrict X inf_le_right (u j : Γ(X, U j))) =
      sectionRestrict X (le_inf hi hj) ((c.transition i j : Γ(X, U i ⊓ U j)) *
        sectionRestrict X inf_le_left (u i : Γ(X, U i))) :=
    congrArg (fun w : (Γ(X, U i ⊓ U j))ˣ =>
      sectionRestrict X (le_inf hi hj) (w : Γ(X, U i ⊓ U j))) (h i j)
  rw [map_mul, map_mul, sectionRestrict_comp, sectionRestrict_comp] at e
  exact e

/-- The cohomology relation is symmetric, through the inverse units. -/
theorem Cohomologous.symm (h : Cohomologous c c' u) :
    Cohomologous c' c (fun i => (u i)⁻¹) := by
  intro i j
  rw [map_inv, map_inv, mul_inv_eq_iff_eq_mul, mul_right_comm, h i j, mul_inv_cancel_right]

/-- Changing the frame of chart `i` of a cocycle by the unit `w i`:
the transition units become `cᵢⱼ wᵢ wⱼ⁻¹`. -/
def twist (c : UnitCocycle U) (w : ∀ i, (Γ(X, U i))ˣ) : UnitCocycle U where
  transition i j := c.transition i j *
    Units.map (sectionRestrict X inf_le_left).toMonoidHom (w i) *
      (Units.map (sectionRestrict X inf_le_right).toMonoidHom (w j))⁻¹
  cocycle i j k V hi hj hk := by
    simp only [map_mul, map_inv, units_map_sectionRestrict_comp]
    have hc := congrArg Units.val (c.cocycle i j k V hi hj hk)
    apply Units.ext
    simp only [Units.val_mul] at hc ⊢
    have hwj := Units.mul_inv (Units.map (sectionRestrict X hj).toMonoidHom (w j))
    rw [← hc]
    linear_combination
      (↑(Units.map (sectionRestrict X (le_inf hi hj)).toMonoidHom (c.transition i j)) *
        ↑(Units.map (sectionRestrict X (le_inf hj hk)).toMonoidHom (c.transition j k)) *
        ↑(Units.map (sectionRestrict X hi).toMonoidHom (w i)) *
        ↑(Units.map (sectionRestrict X hk).toMonoidHom (w k))⁻¹) * hwj

theorem twist_transition (c : UnitCocycle U) (w : ∀ i, (Γ(X, U i))ˣ) (i j : ι) :
    (c.twist w).transition i j = c.transition i j *
      Units.map (sectionRestrict X inf_le_left).toMonoidHom (w i) *
        (Units.map (sectionRestrict X inf_le_right).toMonoidHom (w j))⁻¹ := rfl

/-- A twist is cohomologous to the original cocycle through the twisting units. -/
theorem cohomologous_twist (c : UnitCocycle U) (w : ∀ i, (Γ(X, U i))ˣ) :
    Cohomologous c (c.twist w) w :=
  fun _ _ => inv_mul_cancel_right _ _

section Isomorphism

variable (hU : iSup U = ⊤)

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem cohomologous_compatible (h : Cohomologous c c' u) (i j : ι) (V : X.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) :
    c'.sheaf.val.map (homOfLE hj).op ((u j : Γ(X, U j)) • c'.generator j le_rfl) =
      (c.transitionOn i j hi hj).val •
        c'.sheaf.val.map (homOfLE hi).op ((u i : Γ(X, U i)) • c'.generator i le_rfl) := by
  rw [PresheafOfModules.map_smul, PresheafOfModules.map_smul,
    c'.generator_restrict j (homOfLE hj) le_rfl, c'.generator_restrict i (homOfLE hi) le_rfl,
    c'.generator_transition i j hi hj, smul_smul, smul_smul]
  congr 1
  change sectionRestrict X hj (u j : Γ(X, U j)) * (c'.transitionOn i j hi hj : Γ(X, V)) =
    (c.transitionOn i j hi hj : Γ(X, V)) * sectionRestrict X hi (u i : Γ(X, U i))
  rw [mul_comm]
  exact h.transitionOn i j hi hj

/-- The morphism of glued sheaves sending the generator of chart `i` of `c` to `u i` times the
generator of chart `i` of `c'`. -/
def homOfCohomologous (h : Cohomologous c c' u) : c.sheaf ⟶ c'.sheaf :=
  c.homOfLocalSections c'.sheaf hU (fun i => (u i : Γ(X, U i)) • c'.generator i le_rfl)
    (cohomologous_compatible h)

theorem homOfCohomologous_generator (h : Cohomologous c c' u) (i : ι) :
    (homOfCohomologous hU h).val.app (op (U i)) (c.generator i le_rfl) =
      (u i : Γ(X, U i)) • c'.generator i le_rfl :=
  c.homOfLocalSections_generator _ hU _ _ i

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem homOfCohomologous_comp (h : Cohomologous c c' u) {v : ∀ i, (Γ(X, U i))ˣ}
    (h' : Cohomologous c' c v) (huv : ∀ i, u i * v i = 1) :
    homOfCohomologous hU h ≫ homOfCohomologous hU h' = 𝟙 c.sheaf := by
  apply c.hom_ext_generator hU
  intro i
  change (homOfCohomologous hU h').val.app (op (U i))
      ((homOfCohomologous hU h).val.app (op (U i)) (c.generator i le_rfl)) =
    c.generator i le_rfl
  rw [homOfCohomologous_generator, val_app_smul, homOfCohomologous_generator, smul_smul]
  have e : (u i : Γ(X, U i)) * (v i : Γ(X, U i)) = 1 := congrArg Units.val (huv i)
  rw [e, one_smul]

/-- Cohomologous cocycles glue to isomorphic module sheaves. -/
def sheafIsoOfCohomologous (h : Cohomologous c c' u) : c.sheaf ≅ c'.sheaf where
  hom := homOfCohomologous hU h
  inv := homOfCohomologous hU h.symm
  hom_inv_id := homOfCohomologous_comp hU h h.symm fun i => mul_inv_cancel (u i)
  inv_hom_id := homOfCohomologous_comp hU h.symm h fun i => inv_mul_cancel (u i)

theorem sheafIsoOfCohomologous_hom_generator (h : Cohomologous c c' u) (i : ι) :
    (sheafIsoOfCohomologous hU h).hom.val.app (op (U i)) (c.generator i le_rfl) =
      (u i : Γ(X, U i)) • c'.generator i le_rfl :=
  homOfCohomologous_generator hU h i

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- Every isomorphism of glued sheaves comes from units: the coordinates of the images of the
generators. -/
theorem exists_cohomologous_of_iso (φ : c.sheaf ≅ c'.sheaf) :
    ∃ u : ∀ i, (Γ(X, U i))ˣ, Cohomologous c c' u := by
  let a : ∀ i, Γ(X, U i) := fun i =>
    c'.localSectionsEquiv i le_rfl (φ.hom.val.app (op (U i)) (c.generator i le_rfl))
  let b : ∀ i, Γ(X, U i) := fun i =>
    c.localSectionsEquiv i le_rfl (φ.inv.val.app (op (U i)) (c'.generator i le_rfl))
  have hφ : ∀ (i : ι) (V : X.Opens) (hV : V ≤ U i),
      φ.hom.val.app (op V) (c.generator i hV) =
        sectionRestrict X hV (a i) • c'.generator i hV := by
    intro i V hV
    rw [← c.generator_restrict i (homOfLE hV) le_rfl, PresheafOfModules.naturality_apply,
      ← c'.localSectionsEquiv_smul_generator i le_rfl
        (φ.hom.val.app (op (U i)) (c.generator i le_rfl)),
      PresheafOfModules.map_smul, c'.generator_restrict i (homOfLE hV) le_rfl]
    rfl
  have hba : ∀ i, b i * a i = 1 := by
    intro i
    have h1 : φ.hom.val.app (op (U i)) (φ.inv.val.app (op (U i)) (c'.generator i le_rfl)) =
        c'.generator i le_rfl :=
      congrArg (fun f : c'.sheaf ⟶ c'.sheaf => f.val.app (op (U i)) (c'.generator i le_rfl))
        φ.inv_hom_id
    have h2 := congrArg (c'.localSectionsEquiv i le_rfl) h1
    rw [← c.localSectionsEquiv_smul_generator i le_rfl
        (φ.inv.val.app (op (U i)) (c'.generator i le_rfl)),
      val_app_smul, _root_.map_smul,
      localSectionsEquiv_generator, smul_eq_mul] at h2
    exact h2
  refine ⟨fun i => ⟨a i, b i, by rw [mul_comm]; exact hba i, hba i⟩, fun i j => ?_⟩
  apply Units.ext
  have key := congrArg (φ.hom.val.app (op (U i ⊓ U j)))
    (c.generator_transition i j (inf_le_left : U i ⊓ U j ≤ U i) inf_le_right)
  rw [hφ j _ inf_le_right, val_app_smul, hφ i _ inf_le_left,
    c'.generator_transition i j (inf_le_left : U i ⊓ U j ≤ U i) inf_le_right,
    smul_smul, smul_smul] at key
  have key' := congrArg (c'.localSectionsEquiv i (inf_le_left : U i ⊓ U j ≤ U i)) key
  rw [_root_.map_smul, _root_.map_smul, localSectionsEquiv_generator, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one, transitionOn_inf, transitionOn_inf] at key'
  change (c'.transition i j : Γ(X, U i ⊓ U j)) * sectionRestrict X inf_le_right (a j) =
    (c.transition i j : Γ(X, U i ⊓ U j)) * sectionRestrict X inf_le_left (a i)
  rw [mul_comm]
  exact key'

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem one_compatible (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE hj).op
        (show Γ(SheafOfModules.unit X.ringCatSheaf, U j) from (1 : Γ(X, U j))) =
      ((1 : UnitCocycle U).transitionOn i j hi hj).val •
        (SheafOfModules.unit X.ringCatSheaf).val.map (homOfLE hi).op
          (show Γ(SheafOfModules.unit X.ringCatSheaf, U i) from (1 : Γ(X, U i))) := by
  rw [one_transitionOn, Units.val_one, one_smul]
  change sectionRestrict X hj 1 = sectionRestrict X hi 1
  rw [map_one, map_one]

/-- The morphism from the glued sheaf of the trivial cocycle to the structure sheaf sending
every generator to `1`. -/
def oneSheafHom : (1 : UnitCocycle U).sheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (1 : UnitCocycle U).homOfLocalSections _ hU
    (fun i => show Γ(SheafOfModules.unit X.ringCatSheaf, U i) from (1 : Γ(X, U i)))
    one_compatible

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem oneSheafHom_app (i : ι) (W : X.Opens) (hW : W ≤ U i)
    (s : (1 : UnitCocycle U).sheaf.val.obj (op W)) :
    (oneSheafHom hU).val.app (op W) s = (1 : UnitCocycle U).localSectionsEquiv i hW s := by
  rw [oneSheafHom, homOfLocalSections_apply _ _ _ _ _ i W hW s]
  change (1 : UnitCocycle U).localSectionsEquiv i hW s * sectionRestrict X hW 1 = _
  rw [map_one, mul_one]

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
instance isIso_oneSheafHom : IsIso (oneSheafHom hU) :=
  Scheme.Modules.isIso_of_forall_bijective_app _ fun x => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
    refine ⟨U i, hi, fun W hW => ⟨fun s t hst => ?_, fun y => ?_⟩⟩
    · apply ((1 : UnitCocycle U).localSectionsEquiv i hW).injective
      rw [← oneSheafHom_app hU i W hW, ← oneSheafHom_app hU i W hW]
      exact hst
    · refine ⟨((1 : UnitCocycle U).localSectionsEquiv i hW).symm y, ?_⟩
      rw [oneSheafHom_app hU i W hW]
      exact LinearEquiv.apply_symm_apply _ _

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The trivial cocycle glues to the structure sheaf. -/
def oneSheafIso : (1 : UnitCocycle U).sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  asIso (oneSheafHom hU)

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The glued line bundle of the trivial cocycle is the zero class. -/
theorem classOf_one_lineBundle : classOf X ((1 : UnitCocycle U).lineBundle hU) = 0 :=
  (class_eq_iff X _ _).mpr ⟨oneSheafIso hU ≪≫ (Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)).symm⟩

/-- Two glued line bundles have the same class if and only if the cocycles are
cohomologous. -/
theorem classOf_lineBundle_eq_iff (c c' : UnitCocycle U) :
    classOf X (c.lineBundle hU) = classOf X (c'.lineBundle hU) ↔
      ∃ u : ∀ i, (Γ(X, U i))ˣ, Cohomologous c c' u := by
  constructor
  · intro h
    obtain ⟨φ⟩ := (class_eq_iff X _ _).mp h
    exact exists_cohomologous_of_iso φ
  · rintro ⟨u, hu⟩
    exact (class_eq_iff X _ _).mpr ⟨sheafIsoOfCohomologous hU hu⟩

/-- A glued line bundle is trivial if and only if its cocycle is cohomologous to `1`. -/
theorem classOf_lineBundle_eq_zero_iff (c : UnitCocycle U) :
    classOf X (c.lineBundle hU) = 0 ↔ ∃ u : ∀ i, (Γ(X, U i))ˣ, Cohomologous 1 c u := by
  rw [← classOf_one_lineBundle hU, eq_comm]
  exact classOf_lineBundle_eq_iff hU 1 c

end Isomorphism

end AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle
