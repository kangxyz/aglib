/-
Copyright (c) 2026 R5Lab contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Morphisms
public import Aglib.AlgebraicGeometry.Modules.Support
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Principal-section chains on a two-open cover

Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.PrincipalChain`.

For an arbitrary scheme, two opens covering it, and a section on the first
open which is a unit on the intersection and acts injectively on every
subopen of the first, this module constructs actual line modules with
coefficient transition `a_U = f^n * a_W`. Multiplication by `f` on the first
open and by `1` on the second gives monomorphisms and actual cokernels.
The cokernels vanish on the second open. Their distinguished global section
is the image of the original local frame on the first open, glued with zero.
If the complement of the second open is finite, their actual stalk support is
finite. No Noetherianity, field, normality or cohomology hypothesis is imposed.

The current consumer is the finite projective-line map construction for
proper integral field curves in `Curves/Projectivity`. The curve-specific
constructor discharges the local regularity hypothesis by integrality. The
cohomological stabilization and pencil morphism are separate consumers.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Invertible.PrincipalChain` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`7fb28d626e0ba31b6231991ed5481fbe5cb64c76883728bb9e6d8366c9cee751`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Two opens and a locally regular section which is a unit on their intersection. -/
structure PrincipalChain (X : Scheme.{u}) where
  /-- The first open of the two-open cover. -/
  U : X.Opens
  /-- The second open of the two-open cover. -/
  W : X.Opens
  covers : U ⊔ W = ⊤
  /-- The section on `U` that is regular on subopens and invertible on the overlap. -/
  f : Γ(X, U)
  unit_overlap : IsUnit (sectionRestrict X (inf_le_left : U ⊓ W ≤ U) f)
  regular : ∀ (V : X.Opens) (hV : V ≤ U),
    Function.Injective (fun a : Γ(X, V) => sectionRestrict X hV f * a)

namespace PrincipalChain

variable {X : Scheme.{u}} (d : PrincipalChain X)

/-- The two-element index type for the cover by `U` and `W`. -/
abbrev Index := ULift.{u} Bool

/-- The cover assigning `U` to `true` and `W` to `false`. -/
abbrev cover : Index.{u} → X.Opens
  | ⟨true⟩ => d.U
  | ⟨false⟩ => d.W

theorem iSup_cover : iSup d.cover = ⊤ := by
  apply le_antisymm le_top
  rw [← d.covers]
  exact sup_le (le_iSup d.cover ⟨true⟩) (le_iSup d.cover ⟨false⟩)

/-- The unit on the overlap represented by the restriction of `f`. -/
def overlapUnit : (Γ(X, d.U ⊓ d.W))ˣ := d.unit_overlap.unit

@[simp] theorem overlapUnit_val : (d.overlapUnit : Γ(X, d.U ⊓ d.W)) =
    sectionRestrict X inf_le_left d.f := d.unit_overlap.unit_spec

/-- The transition units given by `f` on `U ∩ W`, its inverse in the reverse direction,
and one on equal charts. -/
def transition : (i j : Index.{u}) → (Γ(X, d.cover i ⊓ d.cover j))ˣ
  | ⟨true⟩, ⟨true⟩ => 1
  | ⟨false⟩, ⟨false⟩ => 1
  | ⟨true⟩, ⟨false⟩ => d.overlapUnit
  | ⟨false⟩, ⟨true⟩ =>
      Units.map (sectionRestrict X (le_inf inf_le_right inf_le_left)).toMonoidHom
        d.overlapUnit⁻¹

theorem transition_cocycle (i j k : Index.{u}) (V : X.Opens)
    (hi : V ≤ d.cover i) (hj : V ≤ d.cover j) (hk : V ≤ d.cover k) :
    Units.map (sectionRestrict X (le_inf hi hj)).toMonoidHom (d.transition i j) *
      Units.map (sectionRestrict X (le_inf hj hk)).toMonoidHom (d.transition j k) =
      Units.map (sectionRestrict X (le_inf hi hk)).toMonoidHom (d.transition i k) := by
  rcases i with ⟨i⟩; rcases j with ⟨j⟩; rcases k with ⟨k⟩
  cases i <;> cases j <;> cases k <;>
    dsimp only [cover] at hi hj hk ⊢ <;>
    simp only [transition, map_one, one_mul, mul_one, map_inv]
  all_goals
    have hm (ha : V ≤ d.W ⊓ d.U) :
        Units.map (sectionRestrict X ha).toMonoidHom
            (Units.map (sectionRestrict X (le_inf inf_le_right inf_le_left)).toMonoidHom
              d.overlapUnit) =
          Units.map (sectionRestrict X (le_inf (ha.trans inf_le_right)
            (ha.trans inf_le_left))).toMonoidHom d.overlapUnit := by
      apply Units.ext
      exact sectionRestrict_comp X _ _ _
    first
    | rw [hm (le_inf hi hj)]; exact inv_mul_cancel _
    | rw [hm (le_inf hj hk)]; exact mul_inv_cancel _

/-- The unit cocycle on the two-open cover determined by the overlap section `f`. -/
def cocycle : UnitCocycle d.cover where
  transition := d.transition
  cocycle := d.transition_cocycle

/-- The actual line module with coefficient transition `f^n`. -/
def line (n : ℕ) : X.Modules := (d.cocycle.zpow (n : ℤ)).sheaf

instance line_finitePresentation (n : ℕ) : (d.line n).IsFinitePresentation :=
  (d.cocycle.zpow (n : ℤ)).isFinitePresentation d.iSup_cover

/-- Original chart projection, retaining the actual subopen. -/
def coefficients (n : ℕ) (i : Index.{u}) {V : X.Opens} (hi : V ≤ d.cover i) :
    Γ(d.line n, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  (d.cocycle.zpow (n : ℤ)).localSectionsEquiv i hi

/-- The original local frame with coefficient one. -/
def frame (n : ℕ) (i : Index.{u}) {V : X.Opens} (hi : V ≤ d.cover i) :
    Γ(d.line n, V) := (d.coefficients n i hi).symm 1

@[simp] theorem coefficients_frame (n : ℕ) (i : Index.{u}) {V : X.Opens}
    (hi : V ≤ d.cover i) : d.coefficients n i hi (d.frame n i hi) = 1 :=
  LinearEquiv.apply_symm_apply _ _

/-- The global section of the first cocycle line with coefficient `f` on `U` and one on `W`. -/
def baseSection : d.cocycle.Sections ⊤ :=
  ⟨fun i => match i with
    | ⟨true⟩ => sectionRestrict X inf_le_right d.f
    | ⟨false⟩ => 1, by
    intro V hV i j hi hj
    rcases i with ⟨i⟩; rcases j with ⟨j⟩
    cases i <;> cases j <;>
      simp only [cocycle, UnitCocycle.transitionOn, transition, map_one, one_mul,
        mul_one, map_inv, Units.val_one, sectionRestrict_comp]
    · have hu :
          Units.map (sectionRestrict X (le_inf hi hj)).toMonoidHom
              (Units.map (sectionRestrict X (le_inf inf_le_right inf_le_left)).toMonoidHom
                d.overlapUnit) =
            Units.map (sectionRestrict X (le_inf hj hi)).toMonoidHom d.overlapUnit := by
        apply Units.ext
        exact sectionRestrict_comp X _ _ _
      rw [hu]
      have hv :
          ((Units.map (sectionRestrict X (le_inf hj hi)).toMonoidHom d.overlapUnit :
            (Γ(X, V))ˣ) : Γ(X, V)) = sectionRestrict X hj d.f := by
        change sectionRestrict X _ (d.overlapUnit : Γ(X,d.U ⊓ d.W)) = _
        rw [overlapUnit_val, sectionRestrict_comp]
      rw [← hv]
      exact (Units.inv_mul _).symm
    · change sectionRestrict X hi d.f =
        sectionRestrict X _ (d.overlapUnit : Γ(X,d.U ⊓ d.W))
      rw [overlapUnit_val, sectionRestrict_comp]
      ⟩

/-- The componentwise product of a section of the first cocycle line with a section of its `n`th
power. -/
def multiplySections (n : ℕ) {V : X.Opens} (a : d.cocycle.Sections V)
    (b : (d.cocycle.zpow (n : ℤ)).Sections V) :
    (d.cocycle.zpow ((n+1 : ℕ) : ℤ)).Sections V :=
  ⟨fun i => a.val i * b.val i, by
    intro T hT i j hi hj
    simp only [map_mul]
    rw [a.property T hT i j hi hj, b.property T hT i j hi hj]
    simp only [UnitCocycle.zpow_transitionOn, zpow_natCast, pow_succ, Units.val_mul]
    ring⟩

/-- The section map from the `n`th line to the next line given by multiplication by the base
section. -/
def stepSections (n : ℕ) (V : X.Opens) :
    Γ(d.line n,V) →ₗ[Γ(X,V)] Γ(d.line (n+1),V) where
  toFun s := d.multiplySections n (d.cocycle.restrictSections le_top d.baseSection) s
  map_add' a b := by
    apply Subtype.ext
    funext i
    exact mul_add _ _ _
  map_smul' r s := by
    apply Subtype.ext
    funext i
    change _ * (sectionRestrict X inf_le_left r * _) =
      sectionRestrict X inf_le_left r * (_ * _)
    ring

/-- Actual multiplication by `f` on `U` and by `1` on `W`. -/
def step (n : ℕ) : d.line n ⟶ d.line (n+1) :=
  ⟨_root_.PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom (d.stepSections n V.unop).toAddMonoidHom
      naturality := by
        intro V T h
        ext s
        apply Subtype.ext
        funext i
        change
          sectionRestrict X (inf_le_inf le_top le_rfl) (d.baseSection.val i) *
              sectionRestrict X (inf_le_inf (leOfHom h.unop) le_rfl) (s.val i) =
            sectionRestrict X (inf_le_inf (leOfHom h.unop) le_rfl)
              (sectionRestrict X (inf_le_inf le_top le_rfl) (d.baseSection.val i) * s.val i)
        rw [map_mul, sectionRestrict_comp] }
    (by intro V r s; exact (d.stepSections n V.unop).map_smul r s)⟩

/-- On every subopen of `U`, the original map multiplies coefficients by `f`. -/
theorem coefficients_step_U (n : ℕ) {V : X.Opens} (hV : V ≤ d.U)
    (s : Γ(d.line n,V)) :
    d.coefficients (n+1) ⟨true⟩ hV ((d.step n).val.app (op V) s) =
      sectionRestrict X hV d.f * d.coefficients n ⟨true⟩ hV s := by
  change sectionRestrict X (le_inf le_rfl hV)
      (sectionRestrict X (inf_le_inf le_top le_rfl)
        (sectionRestrict X inf_le_right d.f) * s.val ⟨true⟩) =
    sectionRestrict X hV d.f * sectionRestrict X (le_inf le_rfl hV) (s.val ⟨true⟩)
  rw [map_mul, sectionRestrict_comp, sectionRestrict_comp]

/-- On every subopen of `W`, the original map preserves coefficients. -/
theorem coefficients_step_W (n : ℕ) {V : X.Opens} (hV : V ≤ d.W)
    (s : Γ(d.line n,V)) :
    d.coefficients (n+1) ⟨false⟩ hV ((d.step n).val.app (op V) s) =
      d.coefficients n ⟨false⟩ hV s := by
  change sectionRestrict X (le_inf le_rfl hV)
      (sectionRestrict X (inf_le_inf le_top le_rfl) (1 : Γ(X,⊤ ⊓ d.W)) *
        s.val ⟨false⟩) = _
  rw [map_one, one_mul]
  rfl

theorem stepSections_injective (n : ℕ) (V : X.Opens) :
    Function.Injective (d.stepSections n V) := by
  intro a b h
  apply Subtype.ext
  funext i
  rcases i with ⟨i⟩
  cases i
  · have hi := congrArg (fun s => s.val ⟨false⟩) h
    simpa [stepSections, multiplySections, baseSection, UnitCocycle.restrictSections_apply]
      using hi
  · apply d.regular (V ⊓ d.U) inf_le_right
    have hi := congrArg (fun s => s.val ⟨true⟩) h
    simpa [stepSections, multiplySections, baseSection, UnitCocycle.restrictSections_apply,
      sectionRestrict_comp] using hi

instance step_mono (n : ℕ) : Mono (d.step n) := by
  have hm : Mono (d.step n).val :=
    PresheafOfModules.mono_of_injective (fun {V} => d.stepSections_injective n V.unop)
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hm

/-- The actual cokernel in the ambient abelian category of module sheaves. -/
def quotient (n : ℕ) : X.Modules := cokernel (d.step n)

/-- The original cokernel projection. -/
def quotientMap (n : ℕ) : d.line (n+1) ⟶ d.quotient n := cokernel.π (d.step n)

/-- The actual short complex formed by the original step and its cokernel. -/
def sequence (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (d.step n) (d.quotientMap n) (cokernel.condition _)

/-- The principal-section chain gives an actual short exact sequence. -/
theorem shortExact (n : ℕ) : (d.sequence n).ShortExact := by
  apply ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (d.step n))
  · change Mono (d.step n)
    infer_instance
  · change Epi (cokernel.π (d.step n))
    infer_instance

/-- The matching global section with coefficients `f^n` on `U` and `1` on `W`. -/
def powerSection (n : ℕ) : Γ(d.line n,⊤) :=
  ⟨fun i => (d.baseSection.val i)^n, by
    intro V hV i j hi hj
    simp only [map_pow]
    rw [d.baseSection.property V hV i j hi hj]
    simp [UnitCocycle.zpow_transitionOn, zpow_natCast, Units.val_pow_eq_pow_val, mul_pow]⟩

theorem powerSection_U (n : ℕ) {V : X.Opens} (hV : V ≤ d.U) :
    d.coefficients n ⟨true⟩ hV
      ((d.line n).val.map (homOfLE le_top).op (d.powerSection n)) =
      sectionRestrict X hV d.f ^ n := by
  change sectionRestrict X (le_inf le_rfl hV)
      (sectionRestrict X (inf_le_inf le_top le_rfl)
        (sectionRestrict X inf_le_right d.f ^ n)) = _
  rw [map_pow, map_pow, sectionRestrict_comp, sectionRestrict_comp]

theorem powerSection_W (n : ℕ) {V : X.Opens} (hV : V ≤ d.W) :
    d.coefficients n ⟨false⟩ hV
      ((d.line n).val.map (homOfLE le_top).op (d.powerSection n)) = 1 := by
  change sectionRestrict X (le_inf le_rfl hV)
      (sectionRestrict X (inf_le_inf le_top le_rfl) ((1 : Γ(X,⊤ ⊓ d.W))^n)) = 1
  simp

theorem step_over_W_isIso (n : ℕ) : IsIso ((d.step n).over d.W) := by
  let e := (d.cocycle.zpow (n : ℤ)).localIso (⟨false⟩ : Index.{u})
  let e' := (d.cocycle.zpow ((n+1 : ℕ) : ℤ)).localIso (⟨false⟩ : Index.{u})
  have he : (d.step n).over d.W ≫ e'.hom = e.hom := by
    apply SheafOfModules.hom_ext
    ext V s
    exact d.coefficients_step_W n (leOfHom V.unop.hom) s
  have hs : (d.step n).over d.W = e.hom ≫ e'.inv := by
    apply (cancel_mono e'.hom).mp
    simp only [Category.assoc, e'.inv_hom_id, Category.comp_id, he]
  rw [hs]
  infer_instance

theorem step_restrict_W_isIso (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor d.W.ι).map (d.step n)) := by
  let := d.step_over_W_isIso n
  have h : IsIso (((SheafOfModules.overFunctor X.ringCatSheaf d.W) ⋙
      (Scheme.Modules.overEquiv d.W).functor).map (d.step n)) := by
    change IsIso ((Scheme.Modules.overEquiv d.W).functor.map ((d.step n).over d.W))
    infer_instance
  exact (NatIso.isIso_map_iff (Scheme.Modules.overFunctorEquiv d.W) (d.step n)).mp h

/-- The actual cokernel restricts to zero on `W`. -/
theorem quotient_zeroOnW (n : ℕ) :
    IsZero ((Scheme.Modules.restrictFunctor d.W.ι).obj (d.quotient n)) := by
  have hi := (Scheme.Modules.supportedAway_isoModSerre_iff d.W.ι (d.step n)).mpr
    (d.step_restrict_W_isIso n)
  exact ((Scheme.Modules.supportedAway d.W.ι).isoModSerre_iff_of_mono (d.step n)).mp hi

theorem quotient_over_W_isZero (n : ℕ) : IsZero ((d.quotient n).over d.W) := by
  let E := (Scheme.Modules.overEquiv d.W).functor
  have hE : IsZero (E.obj ((d.quotient n).over d.W)) :=
    (d.quotient_zeroOnW n).of_iso ((Scheme.Modules.overFunctorEquiv d.W).app (d.quotient n))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply E.map_injective
  rw [E.map_id, E.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp hE

theorem quotient_sectionsOnW_subsingleton (n : ℕ) {V : X.Opens} (hV : V ≤ d.W) :
    Subsingleton (Γ(d.quotient n,V)) := by
  exact ModuleCat.subsingleton_of_isZero
    ((SheafOfModules.evaluation (X.ringCatSheaf.over d.W)
      (op (Over.mk (homOfLE hV)))).map_isZero (d.quotient_over_W_isZero n))

/-- Actual additive stalks of the cokernel vanish at every point of `W`. -/
theorem quotient_stalk_isZero (n : ℕ) (x : X) (hx : x ∈ d.W) :
    IsZero ((Scheme.Modules.stalkFunctor X x).obj (d.quotient n)) :=
  (Scheme.Modules.supportedAway_iff_stalks d.W.ι (d.quotient n)).mp
    (d.quotient_zeroOnW n) ⟨x,hx⟩

theorem quotient_support_subset (n : ℕ) :
    Scheme.Modules.support (d.quotient n) ⊆ (d.W : Set X)ᶜ := by
  intro x hx hxW
  exact hx (d.quotient_stalk_isZero n x hxW)

/-- A finite complement of `W` gives finite actual stalk support. -/
theorem quotient_finiteSupport (n : ℕ) (hW : ((d.W : Set X)ᶜ).Finite) :
    (Scheme.Modules.support (d.quotient n)).Finite :=
  hW.subset (d.quotient_support_subset n)

/-- The local quotient sections given by the image of the frame on `U` and zero on `W`. -/
def quotientLocalSection (n : ℕ) : (i : Index.{u}) → Γ(d.quotient n,d.cover i)
  | ⟨true⟩ => (d.quotientMap n).val.app (op d.U) (d.frame (n+1) ⟨true⟩ le_rfl)
  | ⟨false⟩ => 0

theorem quotientLocalSection_compatible (n : ℕ) :
    TopCat.Presheaf.IsCompatible (d.quotient n).presheaf d.cover (d.quotientLocalSection n) := by
  intro i j
  rcases i with ⟨i⟩; rcases j with ⟨j⟩
  cases i <;> cases j
  · rfl
  · exact @Subsingleton.elim _ (d.quotient_sectionsOnW_subsingleton n inf_le_left) _ _
  · exact @Subsingleton.elim _ (d.quotient_sectionsOnW_subsingleton n inf_le_right) _ _
  · rfl

theorem existsUnique_quotientSection (n : ℕ) :
    ∃! q : Γ(d.quotient n,⊤), ∀ i,
      (d.quotient n).val.map (homOfLE le_top).op q = d.quotientLocalSection n i :=
  TopCat.Sheaf.existsUnique_gluing'
    ⟨(d.quotient n).presheaf,(d.quotient n).isSheaf⟩ d.cover ⊤
    (fun _ => homOfLE le_top) (by rw [d.iSup_cover])
    (d.quotientLocalSection n) (d.quotientLocalSection_compatible n)

/-- The original local quotient frame on `U`, glued with zero on `W`. -/
def quotientSection (n : ℕ) : Γ(d.quotient n,⊤) :=
  Classical.choose (d.existsUnique_quotientSection n)

theorem quotientSection_restrict (n : ℕ) (i : Index.{u}) :
    (d.quotient n).val.map (homOfLE le_top).op (d.quotientSection n) =
      d.quotientLocalSection n i :=
  (Classical.choose_spec (d.existsUnique_quotientSection n)).1 i

/-- The distinguished section is the image of the original local frame on `U`. -/
theorem quotientSection_U (n : ℕ) :
    (d.quotient n).val.map (homOfLE le_top).op (d.quotientSection n) =
      (d.quotientMap n).val.app (op d.U) (d.frame (n+1) ⟨true⟩ le_rfl) :=
  d.quotientSection_restrict n ⟨true⟩

/-- The distinguished section is zero on `W`. -/
theorem quotientSection_W (n : ℕ) :
    (d.quotient n).val.map (homOfLE le_top).op (d.quotientSection n) =
      (0 : Γ(d.quotient n,d.W)) :=
  d.quotientSection_restrict n ⟨false⟩

/-- A lift of the distinguished global section has the original frame image on `U`. -/
theorem quotientMap_lift_U (n : ℕ) (τ : Γ(d.line (n+1),⊤))
    (hτ : (d.quotientMap n).val.app (op ⊤) τ = d.quotientSection n) :
    (d.quotientMap n).val.app (op d.U)
        ((d.line (n+1)).val.map (homOfLE le_top).op τ) =
      (d.quotientMap n).val.app (op d.U) (d.frame (n+1) ⟨true⟩ le_rfl) := by
  rw [PresheafOfModules.naturality_apply (d.quotientMap n).val, hτ]
  exact d.quotientSection_U n

/-- The original section map and cokernel projection are exact on every open.
This uses left exactness of evaluation and the monomorphism of the original step. -/
theorem sections_exact (n : ℕ) (V : X.Opens) :
    ∀ s : Γ(d.line (n+1),V), (d.quotientMap n).val.app (op V) s = 0 →
      ∃ t : Γ(d.line n,V), (d.step n).val.app (op V) t = s := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op V)
  let : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : PreservesFiniteLimits E :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (op V)
  have h : ((d.sequence n).map E).Exact :=
    (d.shortExact n).exact.map_of_mono_of_preservesKernel E
      (by change Mono (d.step n); infer_instance) inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).mp h

/-- A lift of the distinguished quotient generator has coefficient `1 + f*b`
on the entire first open. No affine hypothesis on that open is needed. -/
theorem coefficients_lift_U (n : ℕ) (τ : Γ(d.line (n+1),⊤))
    (hτ : (d.quotientMap n).val.app (op ⊤) τ = d.quotientSection n) :
    ∃ b : Γ(X,d.U),
      d.coefficients (n+1) ⟨true⟩ le_rfl
          ((d.line (n+1)).val.map (homOfLE le_top).op τ) = 1 + d.f * b := by
  let a : Γ(d.line (n+1),d.U) := (d.line (n+1)).val.map (homOfLE le_top).op τ
  let e : Γ(d.line (n+1),d.U) := d.frame (n+1) ⟨true⟩ le_rfl
  have he : (d.quotientMap n).val.app (op d.U) (a-e) = 0 := by
    rw [map_sub, d.quotientMap_lift_U n τ hτ, sub_self]
  obtain ⟨t,ht⟩ := d.sections_exact n d.U (a-e) he
  refine ⟨d.coefficients n ⟨true⟩ le_rfl t, ?_⟩
  have hc := congrArg (d.coefficients (n+1) ⟨true⟩ le_rfl) ht
  rw [d.coefficients_step_U, map_sub, d.coefficients_frame, sectionRestrict_refl] at hc
  exact (sub_eq_iff_eq_add.mp hc.symm).trans (add_comm _ _)

end PrincipalChain
end AlgebraicGeometry.Scheme.Modules.Invertible
