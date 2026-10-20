/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Aglib.AlgebraicGeometry.Modules.Invertible.RationalTrivialization
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.GeometricFibre
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Fibrewise
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.Locality

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.Regular` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`74ba993adf941af5ef35eca75dad28f23ac650a59268faf7a7ff2cc7a063c171`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne LineBundle classOf isLocallyRankOne_iff_local_unit isLocallyRankOne_of_iso
    lineBundle_isLocallyFree pullbackLineBundle)
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
A nonzero morphism from an actual line bundle to the structure sheaf of an
integral scheme is a monomorphism. The proof works on genuine local unit
charts and uses injectivity of restriction on nonempty opens. No additional
mathematical theorem family is retained for this result.
-/

/-!
Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
This module is a new reusable curve foundation for that application.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible Invertible.RationalTrivialization
variable {X : Scheme.{u}} [IsIntegral X] (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit
    X.ringCatSheaf))

theorem lineBundleMap_generator_ne_zero (hφ : φ ≠ 0) (W : X.Opens) [Nonempty W]
    (e : L.val.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W)) :
    φ.app W (chartGenerator X L.val W e) ≠ 0 := by
  intro he
  apply hφ
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  change φ.app V m = 0
  by_cases hV : Nonempty V
  · let := hV
    let : Nonempty ((V ⊓ W) : X.Opens) := nonempty_inf X V W
    apply map_injective_of_isIntegral X (homOfLE inf_le_left : V ⊓ W ⟶ V)
    rw [map_zero]
    have hn := PresheafOfModules.naturality_apply φ.val (homOfLE inf_le_left : V ⊓ W ⟶ V).op m
    change φ.app (V ⊓ W) (L.val.val.map _ m) = X.presheaf.map _ (φ.app V m) at hn
    rw [← hn, lineBundleMap_chart_general L φ W e (V ⊓ W) inf_le_right, he, map_zero, mul_zero]
  · have hv := eq_bot_of_not_nonempty X V hV
    subst V
    exact @Subsingleton.elim Γ(X,⊥) inferInstance _ _

theorem nonzero_lineBundleMap_mono (hφ : φ ≠ 0) : Mono φ := by
  obtain ⟨W, hxW, ⟨e⟩⟩ := (isLocallyRankOne_iff_local_unit X L.val).mp L.property (genericPoint X)
  let : Nonempty W := ⟨⟨genericPoint X, hxW⟩⟩
  have hc := lineBundleMap_generator_ne_zero L φ hφ W e
  have hinj (V : X.Opens) : Function.Injective (φ.app V) := by
    intro m n hmn
    by_cases hV : Nonempty V
    · let := hV
      let : Nonempty ((V ⊓ W) : X.Opens) := nonempty_inf X V W
      apply restrict_injective X L.val L.property (homOfLE inf_le_left : V ⊓ W ⟶ V)
      apply (chartSectionEquiv X L.val W e (V ⊓ W) inf_le_right).injective
      have hres : X.presheaf.map (homOfLE inf_le_right : V ⊓ W ⟶ W).op
          (φ.app W (chartGenerator X L.val W e)) ≠ 0 := by
        intro hz
        apply hc
        exact map_injective_of_isIntegral X (homOfLE inf_le_right : V ⊓ W ⟶ W)
          (hz.trans (map_zero _).symm)
      apply mul_right_cancel₀ hres
      rw [← lineBundleMap_chart_general L φ W e (V ⊓ W) inf_le_right,
        ← lineBundleMap_chart_general L φ W e (V ⊓ W) inf_le_right]
      exact (PresheafOfModules.naturality_apply φ.val (homOfLE inf_le_left : V ⊓ W ⟶ V).op m).trans
        ((congrArg (X.presheaf.map (homOfLE inf_le_left : V ⊓ W ⟶ V).op) hmn).trans
          (PresheafOfModules.naturality_apply φ.val (homOfLE inf_le_left : V ⊓ W ⟶ V).op n).symm)
    · have hv := eq_bot_of_not_nonempty X V hV
      subst V
      let : Subsingleton Γ((show X.Modules from L.val),⊥) :=
        Module.subsingleton Γ(X,⊥) _
      exact Subsingleton.elim _ _
  constructor
  intro Z a b hab
  apply Scheme.Modules.hom_ext
  intro V
  ext m
  apply hinj V
  exact congrArg (fun k : Z ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ↦ k.app
      V m) hab
end AlgebraicGeometry.Scheme.Modules.Invertible

/-!
The following two general source families are separate and explicit.
FibrewiseRegularLineBundle is a derived all-flat-LFP-schemes corollary of
Stacks 062Y, Lemma 31.19.9(3). A line-bundle-to-unit map has locally principal
image; geometric-fibre monicity makes each local generator regular. The
retained source bridge includes faithful-flat residue-field descent and the
compatibility of the independently constructed image-ideal zero scheme with
the pulled fibre map. It yields actual monicity and flatness of the actual
zero scheme, with no genus, degree, graph or Abel conclusion.

SmoothRelativeCartierLocality is the reverse direction (2) implies (3) of
Stacks 0B9D, Lemma 44.3.1: for a smooth relative curve, an actual closed
immersion with invertible ideal and flat quotient is locally quasi-finite
and locally finitely presented over the base. The actual kernel ideal is the
effective Cartier ideal (01WQ/01WR). Both families allow arbitrary nonreduced
and non-Noetherian bases. Exact source statements and correction comments
were inspected on 2026-10-09; the above specializations are disclosed derived
corollaries. Proper implies finite is proved by the pinned native theorem.
-/
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible
variable {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit
    X.ringCatSheaf))
/-- The theorem-family input asserting that geometric-fibre regularity of a line-bundle map
over a flat locally finitely presented family gives a monomorphism and a flat zero scheme. -/
def FibrewiseRegularLineBundle : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S) (L : LineBundle X)
    (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)),
    Flat f → LocallyOfFinitePresentation f → GeometricFibreRegular f L φ →
      Mono φ ∧ Flat (zeroInclusion φ ≫ f)

variable {f}
/-- The identification of a line bundle embedded in the unit module with its zero-scheme ideal. -/
def zeroIdealLineBundleIso [Mono φ] : L.val ≅ idealModule (zeroInclusion φ) := by
  let := lineBundle_isLocallyFree X L
  let : L.val.IsQuasicoherent := inferInstance
  let h := imageIdealLocalizes_of_isQuasicoherent φ
  let := zeroIdealFactor_isIso φ h
  let e := asIso (zeroIdealFactor φ h)
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- The zero-scheme ideal as a line bundle, when the given line-bundle map is monic. -/
def zeroIdealLineBundle [Mono φ] : LineBundle X :=
  ⟨idealModule (zeroInclusion φ), isLocallyRankOne_of_iso X (zeroIdealLineBundleIso L φ) L.property⟩

@[simp] theorem zeroIdealLineBundle_class [Mono φ] :
    classOf X (zeroIdealLineBundle L φ) = classOf X L := by
  apply Quotient.sound
  exact ⟨(zeroIdealLineBundleIso L φ).symm⟩
end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible
/-- The theorem-family input asserting local quasi-finiteness and local finite presentation
for a relative flat Cartier subscheme of a smooth relative curve. -/
def SmoothRelativeCartierLocality : Prop :=
  ∀ (S X D : Scheme.{u}) (p : X ⟶ S) (i : D ⟶ X),
    SmoothOfRelativeDimension 1 p → IsClosedImmersion i →
      IsLocallyRankOne X (idealModule i) → Flat (i ≫ p) →
        LocallyQuasiFinite (i ≫ p) ∧ LocallyOfFinitePresentation (i ≫ p)

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : LineBundle X)
variable (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit
    X.ringCatSheaf))
theorem regularZero_finite_flat
    (hregular : FibrewiseRegularLineBundle.{u}) (hlocal : SmoothRelativeCartierLocality.{u})
    [SmoothOfRelativeDimension 1 f] [IsProper f] (hφ : GeometricFibreRegular f L φ) :
    IsFinite (zeroInclusion φ ≫ f) ∧ Flat (zeroInclusion φ ≫ f) ∧
      LocallyOfFinitePresentation (zeroInclusion φ ≫ f) := by
  let := SmoothOfRelativeDimension.smooth 1 f
  obtain ⟨hm, hflat⟩ := hregular X S f L φ inferInstance inferInstance hφ
  let := hm
  let := hflat
  have h := hlocal S X (zeroScheme φ) f (zeroInclusion φ) inferInstance inferInstance
    (zeroIdealLineBundle L φ).property hflat
  let := h.1
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite (zeroInclusion φ ≫ f), hflat, h.2⟩

/-- The native fibrewise regularity theorem supplies the unchanged actual zero-scheme interface. -/
theorem fibrewiseRegularLineBundle : FibrewiseRegularLineBundle.{u} :=
  mono_and_flat_zeroInclusion_comp_of_geometricFibreRegular

/-- Native smooth-Cartier locality supplies the original general locality interface. -/
theorem smoothRelativeCartierLocality : SmoothRelativeCartierLocality.{u} :=
  Scheme.Hom.locallyQuasiFinite_and_locallyOfFinitePresentation_of_smooth_cartier

end AlgebraicGeometry.Scheme.Modules.Invertible
