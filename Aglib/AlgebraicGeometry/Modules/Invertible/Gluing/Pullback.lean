/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Morphisms

/-!
# Pullback of a line module glued from a unit cocycle

Let `f : X ⟶ Y` be a morphism of schemes, `c` a unit cocycle on an open cover `U` of `Y`, and
`c'` a unit cocycle on a family `U'` of opens of `X` with `f⁻¹(U i) = U' i`, whose transition
units are the images under `f` of those of `c` (`TransitionPullback`). Then
`f^* c.sheaf ≅ c'.sheaf` (`UnitCocycle.pullbackIso`), and the isomorphism sends the pulled-back
generator of each chart to the generator of the same chart
(`pullbackIso_hom_pullbackGenerator`). In coordinates: the line module with transition
functions `gᵢⱼ` pulls back to the line module with transition functions `f^# gᵢⱼ`.

The forward map is adjoint to the morphism `c.sheaf ⟶ f_* c'.sheaf` that sends the generators
of `c` to those of `c'` (`toPushforward`, by `homOfLocalSections`). The inverse sends the
generators of `c'` to the adjunction-unit images of the generators of `c` (`toPullback`). Both
composites are identities because a morphism out of a glued sheaf is determined by the images
of the chart generators (`hom_ext_generator`). No local trivialization of the pullback is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle

section Generator

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (c : UnitCocycle U)

/-- The standard generator on a subopen of the `i` chart: the section whose `i` frame
coefficient is one. -/
def generator (i : ι) {V : X.Opens} (hV : V ≤ U i) : Γ(c.sheaf, V) :=
  (c.localSectionsEquiv i hV).symm 1

/-- The generator has frame coefficient one. -/
@[simp]
theorem localSectionsEquiv_generator (i : ι) {V : X.Opens} (hV : V ≤ U i) :
    c.localSectionsEquiv i hV (c.generator i hV) = 1 :=
  (c.localSectionsEquiv i hV).apply_symm_apply 1

/-- Restricting a generator along any inclusion gives the generator of the smaller open. -/
theorem generator_restrict (i : ι) {V W : X.Opens} (g : V ⟶ W) (hW : W ≤ U i) :
    c.sheaf.val.map g.op (c.generator i hW) = c.generator i ((leOfHom g).trans hW) := by
  apply (c.localSectionsEquiv i ((leOfHom g).trans hW)).injective
  rw [localSectionsEquiv_generator]
  exact (c.localSectionsEquiv_restrict i (leOfHom g) hW (c.generator i hW)).trans
    (by rw [localSectionsEquiv_generator, map_one])

-- Sections are matched across `Γ(X, V)`, `Γ(M, V)` and the module-sheaf presentations
-- (`X.ringCatSheaf`, `M.val`), as in the upstream gluing files.
set_option backward.isDefEq.respectTransparency false in
/-- Every section on a subopen of a chart is its frame coefficient times the generator. -/
theorem localSectionsEquiv_smul_generator (i : ι) {V : X.Opens} (hV : V ≤ U i)
    (s : Γ(c.sheaf, V)) : c.localSectionsEquiv i hV s • c.generator i hV = s := by
  apply (c.localSectionsEquiv i hV).injective
  rw [_root_.map_smul, localSectionsEquiv_generator, smul_eq_mul, mul_one]

-- Sections are matched across `Γ(X, V)`, `Γ(M, V)` and the module-sheaf presentations
-- (`X.ringCatSheaf`, `M.val`), as in the upstream gluing files.
set_option backward.isDefEq.respectTransparency false in
/-- The generators satisfy the inverse of the coefficient transition rule. -/
theorem generator_transition (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) :
    c.generator j hj = (c.transitionOn i j hi hj : Γ(X, V)) • c.generator i hi := by
  apply (c.localSectionsEquiv i hi).injective
  rw [c.localSectionsEquiv_transition i j hi hj, _root_.map_smul, localSectionsEquiv_generator,
    localSectionsEquiv_generator, smul_eq_mul]

-- Sections are matched across `Γ(X, V)`, `Γ(M, V)` and the module-sheaf presentations
-- (`X.ringCatSheaf`, `M.val`), as in the upstream gluing files.
set_option backward.isDefEq.respectTransparency false in
/-- Morphisms out of the glued sheaf are determined by the images of the chart generators. -/
theorem hom_ext_generator (hU : iSup U = ⊤) {M : X.Modules} {g h : c.sheaf ⟶ M}
    (hgh : ∀ i, g.val.app (op (U i)) (c.generator i le_rfl) =
      h.val.app (op (U i)) (c.generator i le_rfl)) : g = h := by
  ext V s
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, hU, inf_top_eq])
  intro i
  change M.val.map (homOfLE inf_le_left).op (g.val.app (op V) s) =
    M.val.map (homOfLE inf_le_left).op (h.val.app (op V) s)
  rw [← PresheafOfModules.naturality_apply g.val, ← PresheafOfModules.naturality_apply h.val,
    ← c.localSectionsEquiv_smul_generator i (inf_le_right : V ⊓ U i ≤ U i)
      (c.sheaf.val.map (homOfLE inf_le_left).op s),
    ← c.generator_restrict i (homOfLE (inf_le_right : V ⊓ U i ≤ U i)) le_rfl,
    _root_.map_smul, _root_.map_smul, PresheafOfModules.naturality_apply g.val,
    PresheafOfModules.naturality_apply h.val, hgh i]

end Generator

section Pullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} {U : ι → Y.Opens} {U' : ι → X.Opens}
  (c : UnitCocycle U) (c' : UnitCocycle U')

/-- The transition units of `c'` are the images under `f` of the transition units of `c`. -/
def TransitionPullback : Prop :=
  ∀ (i j : ι) (e : U' i ⊓ U' j ≤ f ⁻¹ᵁ (U i ⊓ U j)),
    Units.map (f.appLE (U i ⊓ U j) (U' i ⊓ U' j) e).hom.toMonoidHom (c.transition i j) =
      c'.transition i j

variable {f c c'}

/-- Integer powers of compatible transition units are compatible. -/
theorem TransitionPullback.zpow (ht : TransitionPullback f c c') (n : ℤ) :
    TransitionPullback f (c.zpow n) (c'.zpow n) := by
  intro i j e
  rw [zpow_transition, zpow_transition, map_zpow, ht i j e]

/-- The pairwise overlaps of `U'` lie over the overlaps of `U`. -/
theorem inf_le_preimage_inf (hU : ∀ i, f ⁻¹ᵁ U i = U' i) (i j : ι) :
    U' i ⊓ U' j ≤ f ⁻¹ᵁ (U i ⊓ U j) := by
  rw [Scheme.Hom.preimage_inf, hU i, hU j]

/-- A family with `f⁻¹(U i) = U' i` covers `X` when `U` covers `Y`. -/
theorem iSup_eq_top_of_preimage (hU : ∀ i, f ⁻¹ᵁ U i = U' i) (hYU : iSup U = ⊤) :
    iSup U' = ⊤ := by
  have h : U' = fun i => f ⁻¹ᵁ U i := funext fun i => (hU i).symm
  rw [h, ← Scheme.Hom.preimage_iSup, hYU, Scheme.Hom.preimage_top]

/-- Compatible transition units agree after restriction to every common subopen. -/
theorem TransitionPullback.appLE_transitionOn (ht : TransitionPullback f c c')
    (hU : ∀ i, f ⁻¹ᵁ U i = U' i) (i j : ι) {W : Y.Opens} {V : X.Opens}
    (hi : W ≤ U i) (hj : W ≤ U j) (hi' : V ≤ U' i) (hj' : V ≤ U' j) (e : V ≤ f ⁻¹ᵁ W) :
    (f.appLE W V e).hom (c.transitionOn i j hi hj : Γ(Y, W)) =
      (c'.transitionOn i j hi' hj' : Γ(X, V)) := by
  have h := congrArg (fun u : (Γ(X, U' i ⊓ U' j))ˣ => sectionRestrict X (le_inf hi' hj') u.val)
    (ht i j (inf_le_preimage_inf hU i j))
  refine Eq.trans ?_ h
  change (Y.presheaf.map (homOfLE (le_inf hi hj)).op ≫ f.appLE W V e).hom
      (c.transition i j).val =
    (f.appLE (U i ⊓ U j) (U' i ⊓ U' j) (inf_le_preimage_inf hU i j) ≫
      X.presheaf.map (homOfLE (le_inf hi' hj')).op).hom (c.transition i j).val
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

variable (f c)

/-- The pulled-back generator of the `i` chart, on a subopen of `f⁻¹(U i)`: the restriction of
the adjunction-unit image of the generator. -/
def pullbackGenerator (i : ι) {V : X.Opens} (hV : V ≤ f ⁻¹ᵁ U i) :
    Γ((pullback f).obj c.sheaf, V) :=
  ((pullback f).obj c.sheaf).val.map (homOfLE hV).op
    (((pullbackPushforwardAdjunction f).unit.app c.sheaf).val.app (op (U i))
      (c.generator i le_rfl))

/-- On the whole inverse-image chart, the pulled-back generator is the unit image. -/
theorem pullbackGenerator_self (i : ι) :
    c.pullbackGenerator f i (le_refl (f ⁻¹ᵁ U i)) =
      ((pullbackPushforwardAdjunction f).unit.app c.sheaf).val.app (op (U i))
        (c.generator i le_rfl) := by
  change ((pullback f).obj c.sheaf).val.map (𝟙 (op (f ⁻¹ᵁ U i))) _ = _
  rw [((pullback f).obj c.sheaf).val.map_id]
  rfl

-- Sections are matched across `Γ(X, V)`, `Γ(M, V)` and the module-sheaf presentations
-- (`X.ringCatSheaf`, `M.val`), as in the upstream gluing files.
set_option backward.isDefEq.respectTransparency false in
/-- Restricting a pulled-back generator gives the pulled-back generator of the smaller open. -/
theorem pullbackGenerator_restrict (i : ι) {V W : X.Opens} (g : V ⟶ W)
    (hW : W ≤ f ⁻¹ᵁ U i) :
    ((pullback f).obj c.sheaf).val.map g.op (c.pullbackGenerator f i hW) =
      c.pullbackGenerator f i ((leOfHom g).trans hW) := by
  rw [pullbackGenerator, pullbackGenerator, ← PresheafOfModules.map_comp_apply]
  rfl

-- Sections are matched across `Γ(X, V)`, `Γ(M, V)` and the module-sheaf presentations
-- (`X.ringCatSheaf`, `M.val`), as in the upstream gluing files.
set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back generators satisfy the pulled-back transition rule. -/
theorem pullbackGenerator_transition (i j : ι) {V : X.Opens} (hi : V ≤ f ⁻¹ᵁ U i)
    (hj : V ≤ f ⁻¹ᵁ U j) (e : V ≤ f ⁻¹ᵁ (U i ⊓ U j)) :
    c.pullbackGenerator f j hj =
      (f.appLE (U i ⊓ U j) V e).hom
          (c.transitionOn i j inf_le_left inf_le_right : Γ(Y, U i ⊓ U j)) •
        c.pullbackGenerator f i hi := by
  let N := (pullback f).obj c.sheaf
  let η : c.sheaf ⟶ (pushforward f).obj N := (pullbackPushforwardAdjunction f).unit.app c.sheaf
  have h₀ := congrArg (η.val.app (op (U i ⊓ U j)))
    (c.generator_transition i j (inf_le_left : U i ⊓ U j ≤ U i) inf_le_right)
  rw [_root_.map_smul] at h₀
  rw [← c.generator_restrict i (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) le_rfl,
    ← c.generator_restrict j (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) le_rfl,
    PresheafOfModules.naturality_apply η.val, PresheafOfModules.naturality_apply η.val] at h₀
  change c.pullbackGenerator f j
      (leOfHom ((Opens.map f.base).map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)))) =
    (f.app (U i ⊓ U j)).hom (c.transitionOn i j inf_le_left inf_le_right : Γ(Y, U i ⊓ U j)) •
      c.pullbackGenerator f i
        (leOfHom ((Opens.map f.base).map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)))) at h₀
  have h₁ := congrArg (N.val.map (homOfLE e).op) h₀
  rw [PresheafOfModules.map_smul, pullbackGenerator_restrict, pullbackGenerator_restrict] at h₁
  exact h₁

variable (c')
variable (hU : ∀ i, f ⁻¹ᵁ U i = U' i) (ht : TransitionPullback f c c') (hYU : iSup U = ⊤)

-- Sections are matched across `Γ(X, V)`, `Γ(M, V)` and the module-sheaf presentations
-- (`X.ringCatSheaf`, `M.val`), as in the upstream gluing files.
set_option backward.isDefEq.respectTransparency false in
/-- The morphism `c.sheaf ⟶ f_* c'.sheaf` sending each generator of `c` to the generator of
`c'` on the inverse-image chart. -/
def toPushforward : c.sheaf ⟶ (pushforward f).obj c'.sheaf :=
  c.homOfLocalSections ((pushforward f).obj c'.sheaf) hYU
    (fun i => c'.generator i (hU i).le) (by
      intro i j V hi hj
      change c'.sheaf.val.map ((Opens.map f.base).map (homOfLE hj)).op
          (c'.generator j (hU j).le) =
        (f.app V).hom (c.transitionOn i j hi hj : Γ(Y, V)) •
          c'.sheaf.val.map ((Opens.map f.base).map (homOfLE hi)).op (c'.generator i (hU i).le)
      rw [generator_restrict, generator_restrict, Scheme.Hom.app_eq_appLE,
        ht.appLE_transitionOn hU i j hi hj
          ((leOfHom ((Opens.map f.base).map (homOfLE hi))).trans (hU i).le)
          ((leOfHom ((Opens.map f.base).map (homOfLE hj))).trans (hU j).le) le_rfl,
        ← generator_transition])

/-- `toPushforward` sends the generator of each chart to the generator of `c'`. -/
theorem toPushforward_generator (i : ι) :
    (c.toPushforward f c' hU ht hYU).val.app (op (U i)) (c.generator i le_rfl) =
      c'.generator i (hU i).le :=
  c.homOfLocalSections_generator _ hYU _ _ i

-- Sections are matched across `Γ(X, V)`, `Γ(M, V)` and the module-sheaf presentations
-- (`X.ringCatSheaf`, `M.val`), as in the upstream gluing files.
set_option backward.isDefEq.respectTransparency false in
/-- The morphism `c'.sheaf ⟶ f^* c.sheaf` sending each generator of `c'` to the pulled-back
generator of `c`. -/
def toPullback : c'.sheaf ⟶ (pullback f).obj c.sheaf :=
  c'.homOfLocalSections ((pullback f).obj c.sheaf) (iSup_eq_top_of_preimage hU hYU)
    (fun i => c.pullbackGenerator f i (hU i).ge) (by
      intro i j V hi hj
      rw [pullbackGenerator_restrict, pullbackGenerator_restrict,
        c.pullbackGenerator_transition f i j _ _ (le_inf (hi.trans (hU i).ge)
          (hj.trans (hU j).ge)),
        ht.appLE_transitionOn hU i j inf_le_left inf_le_right hi hj])

/-- `toPullback` sends the generator of each chart to the pulled-back generator. -/
theorem toPullback_generator (i : ι) :
    (c.toPullback f c' hU ht hYU).val.app (op (U' i)) (c'.generator i le_rfl) =
      c.pullbackGenerator f i (hU i).ge :=
  c'.homOfLocalSections_generator _ (iSup_eq_top_of_preimage hU hYU) _ _ i

/-- The comparison `f^* c.sheaf ⟶ c'.sheaf`, adjoint to `toPushforward`. -/
def pullbackHom : (pullback f).obj c.sheaf ⟶ c'.sheaf :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm (c.toPushforward f c' hU ht hYU)

/-- The adjunction unit followed by the direct image of `pullbackHom` is `toPushforward`. -/
@[reassoc]
theorem unit_comp_pullbackHom :
    (pullbackPushforwardAdjunction f).unit.app c.sheaf ≫
        (pushforward f).map (c.pullbackHom f c' hU ht hYU) =
      c.toPushforward f c' hU ht hYU :=
  ((pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- `unit_comp_pullbackHom` on sections. -/
theorem pullbackHom_app_unit (W : Y.Opens) (s : Γ(c.sheaf, W)) :
    (c.pullbackHom f c' hU ht hYU).val.app (op (f ⁻¹ᵁ W))
        (((pullbackPushforwardAdjunction f).unit.app c.sheaf).val.app (op W) s) =
      (c.toPushforward f c' hU ht hYU).val.app (op W) s :=
  congrArg (fun φ => φ.val.app (op W) s) (c.unit_comp_pullbackHom f c' hU ht hYU)

-- Sections are matched across `Γ(X, V)`, `Γ(M, V)` and the module-sheaf presentations
-- (`X.ringCatSheaf`, `M.val`), as in the upstream gluing files.
set_option backward.isDefEq.respectTransparency false in
/-- The comparison sends each pulled-back generator to the generator of `c'`. -/
theorem pullbackHom_pullbackGenerator (i : ι) {V : X.Opens} (hV : V ≤ f ⁻¹ᵁ U i) :
    (c.pullbackHom f c' hU ht hYU).val.app (op V) (c.pullbackGenerator f i hV) =
      c'.generator i (hV.trans (hU i).le) := by
  rw [pullbackGenerator, PresheafOfModules.naturality_apply, pullbackHom_app_unit,
    toPushforward_generator, generator_restrict]

-- Sections are matched across `Γ(X, V)`, `Γ(M, V)` and the module-sheaf presentations
-- (`X.ringCatSheaf`, `M.val`), as in the upstream gluing files.
set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison sends each generator of `c'` to the pulled-back generator. -/
theorem toPullback_generator_of_le (i : ι) {V : X.Opens} (hV : V ≤ U' i) :
    (c.toPullback f c' hU ht hYU).val.app (op V) (c'.generator i hV) =
      c.pullbackGenerator f i (hV.trans (hU i).ge) := by
  rw [← c'.generator_restrict i (homOfLE hV) le_rfl, PresheafOfModules.naturality_apply,
    toPullback_generator, pullbackGenerator_restrict]

/-- The pullback of the glued sheaf of `c` is the glued sheaf of `c'`. -/
def pullbackIso : (pullback f).obj c.sheaf ≅ c'.sheaf where
  hom := c.pullbackHom f c' hU ht hYU
  inv := c.toPullback f c' hU ht hYU
  hom_inv_id := by
    apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_id,
      Adjunction.homEquiv_unit, unit_comp_pullbackHom]
    apply c.hom_ext_generator hYU
    intro i
    change (c.toPullback f c' hU ht hYU).val.app (op (f ⁻¹ᵁ U i))
        ((c.toPushforward f c' hU ht hYU).val.app (op (U i)) (c.generator i le_rfl)) = _
    rw [toPushforward_generator, toPullback_generator_of_le]
    exact c.pullbackGenerator_self f i
  inv_hom_id := by
    apply c'.hom_ext_generator (iSup_eq_top_of_preimage hU hYU)
    intro i
    change (c.pullbackHom f c' hU ht hYU).val.app (op (U' i))
        ((c.toPullback f c' hU ht hYU).val.app (op (U' i)) (c'.generator i le_rfl)) =
      c'.generator i le_rfl
    rw [toPullback_generator, pullbackHom_pullbackGenerator]

@[simp]
theorem pullbackIso_hom : (c.pullbackIso f c' hU ht hYU).hom = c.pullbackHom f c' hU ht hYU :=
  rfl

@[simp]
theorem pullbackIso_inv : (c.pullbackIso f c' hU ht hYU).inv = c.toPullback f c' hU ht hYU :=
  rfl

/-- The pullback isomorphism sends the pulled-back generator to the generator, on every
subopen of every chart. -/
theorem pullbackIso_hom_pullbackGenerator (i : ι) {V : X.Opens} (hV : V ≤ U' i) :
    (c.pullbackIso f c' hU ht hYU).hom.val.app (op V)
        (c.pullbackGenerator f i (hV.trans (hU i).ge)) = c'.generator i hV :=
  c.pullbackHom_pullbackGenerator f c' hU ht hYU i _

/-- The inverse pullback isomorphism sends the generator to the pulled-back generator. -/
theorem pullbackIso_inv_generator (i : ι) {V : X.Opens} (hV : V ≤ U' i) :
    (c.pullbackIso f c' hU ht hYU).inv.val.app (op V) (c'.generator i hV) =
      c.pullbackGenerator f i (hV.trans (hU i).ge) :=
  c.toPullback_generator_of_le f c' hU ht hYU i hV

end Pullback

end AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle
