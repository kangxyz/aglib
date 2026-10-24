/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveBundle.RankTwoExtension.Conormal.Compatibility
public import Aglib.AlgebraicGeometry.ProjectiveBundle.RankTwoExtension.Complement
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Avoidance
public import Aglib.AlgebraicGeometry.IdealSheaf.Modules.ConormalMap
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.VerticalCartier
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalFunctions
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# Splitting from a concrete finite normal extension graph

A concrete finite morphism from an integral normal scheme to the original
rank-two projective bundle splits the original extension when its projection
is birational and its generically avoided quotient-section intersection is
vertical over a normal local surface. The actual Cartier ideal, conormal map,
open-complement factorization and original function-field map are retained.

The intended graph is the finite normalization of the actual image of the
punctured complementary section. This result does not construct that finite
normalization or assert punctured H1 injectivity. No Nagata hypothesis is
needed once the concrete finite graph has been supplied.

Source: the graph and vertical-Cartier argument in Stacks Project,
Lemma 54.7.5, tag 0AXB, using Lemma 54.7.4, tag 0AXA.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

universe u

variable {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
  [IsNoetherianRing A] [IsIntegrallyClosed A]
  {X N : Scheme.{u}} {E : X.Modules} [IsIntegral N]
  (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
  (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  (hig : i ≫ g = 0)
  (hS : (extensionComplex i g hig).ShortExact)

local notation "ℙ" => projectiveBundle i g hig hS
local notation "σ" => quotientSection i g hig hS

/-- The actual intersection on a normal surface modification cannot be
nonempty, vertical, and generically avoided. The conormal is transported
through the original canonical ideal-pullback map. -/
private theorem quotientIntersection_not_nonempty
    (qN : N ⟶ Spec (.of A)) [IsProper qN] [IsDominant qN]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap qN)))
    (hdim : ringKrullDim A = 2) (hN : NormalStalks N)
    (h : N ⟶ ℙ) (havoid : ¬ Set.range h ⊆ Set.range σ)
    (hvertical : ∀ z : Limits.pullback (C := Scheme.{u}) σ h,
      qN (Limits.pullback.snd σ h z) = IsLocalRing.closedPoint A) :
    ¬ Nonempty (Limits.pullback (C := Scheme.{u}) σ h) := by
  intro hZ
  let : Nonempty (Limits.pullback (C := Scheme.{u}) σ h) := hZ
  let j := Limits.pullback.snd σ h
  let a := Limits.pullback.fst σ h
  have hsquare : a ≫ σ = j ≫ h := Limits.pullback.condition
  let c := Scheme.Hom.idealPullbackMap σ j h a hsquare
  let hc : IsIso c := Scheme.Hom.idealPullbackMap_isIso_of_integral_avoidance
    σ j h a hsquare (IsPullback.of_hasPullback σ h)
      (quotientIdeal_locallyRankOne i g hig hS) havoid
  have hj : IsLocallyRankOne N (Scheme.Hom.idealModule j) :=
    isLocallyRankOne_of_iso N (@asIso _ _ _ _ c hc)
      (pullback_locallyRankOne h (Scheme.Hom.idealModule σ)
        (quotientIdeal_locallyRankOne i g hig hS))
  let d := Scheme.Hom.conormalSquareMap σ j h a hsquare
  let : IsIso d := by
    dsimp [d, Scheme.Hom.conormalSquareMap]
    infer_instance
  let e : (Modules.pullback j).obj (Scheme.Hom.idealModule j) ≅
      SheafOfModules.unit (Limits.pullback σ h).ringCatSheaf :=
    (asIso d).symm ≪≫
      (Modules.pullback a).mapIso
        (quotientConormalIso g i hig hS) ≪≫
      Modules.pullbackUnitIso a
  exact VerticalCartier.conormal_not_trivial_of_vertical_cartier
    qN hff hdim hN j hj hvertical ⟨e⟩

/-- An affine proper birational morphism to an integral normal scheme is
an isomorphism, through the original structural ring-sheaf map. -/
private theorem isIso_of_affine_proper_birational
    {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
    (r : Y ⟶ T) [IsAffineHom r] [IsProper r] [IsDominant r]
    (hT : NormalStalks T)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap r))) : IsIso r := by
  let : IsIso r.c := isIso_c_of_isProper_birational r hT hff
  apply (IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme)
    (fun V : T.affineOpens => V.1) (iSup_affineOpens_eq_top T)).mpr
  intro V
  apply (isIso_morphismRestrict_iff_isIso_app r V.2).mpr
  exact NatIso.isIso_app_of_isIso r.c (op V.1)

/-- A concrete finite normal graph over the original projective bundle
produces a splitting. The hypotheses are properties of the supplied
actual map h; no existence of finite normalization is asserted.

For the intended application h = ν ≫ τ.imageι, where τ is the original
punctured complementary section and ν is its concrete finite normalization.
The graph closure still has to supply generic avoidance, verticality and
the original birational function-field map. -/
theorem splitting_of_finite_normal_graph
    [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hdim : ringKrullDim A = 2) (hX : NormalStalks X) (hN : NormalStalks N)
    (h : N ⟶ ℙ) [IsFinite h]
    [IsDominant (h ≫ projection i g hig hS)]
    (hffh : IsIso (CommRingCat.ofHom (functionFieldMap
      (h ≫ projection i g hig hS))))
    (havoid : ¬ Set.range h ⊆ Set.range σ)
    (hvertical : ∀ z : Limits.pullback (C := Scheme.{u}) σ h,
      ((h ≫ projection i g hig hS) ≫ f)
        (Limits.pullback.snd σ h z) = IsLocalRing.closedPoint A) :
    Nonempty ((extensionComplex i g hig).Splitting) := by
  let r := h ≫ projection i g hig hS
  let C := quotientComplement i g hig hS
  let : IsIso (CommRingCat.ofHom (functionFieldMap f)) := hff
  let : IsIso (CommRingCat.ofHom (functionFieldMap r)) := hffh
  have hffr : IsIso (CommRingCat.ofHom (functionFieldMap (r ≫ f))) := by
    rw [functionFieldMap_comp]
    change IsIso (CommRingCat.ofHom (functionFieldMap f) ≫
      CommRingCat.ofHom (functionFieldMap r))
    infer_instance
  have hZ := quotientIntersection_not_nonempty i g hig hS
    (r ≫ f) hffr hdim hN h havoid hvertical
  have hC : Set.range h ⊆ Set.range C.ι := by
    rintro _ ⟨n, rfl⟩
    rw [Scheme.Opens.range_ι]
    change h n ∉ Set.range σ
    rintro ⟨x, hx⟩
    obtain ⟨z, _, _⟩ := exists_preimage_of_isPullback
      (IsPullback.of_hasPullback σ h) x n hx
    exact hZ ⟨z⟩
  let t : N ⟶ C.toScheme := IsOpenImmersion.lift C.ι h hC
  have ht : t ≫ C.ι = h := IsOpenImmersion.lift_fac _ _ _
  let : IsAffineHom (t ≫ C.ι) := by rw [ht]; infer_instance
  let : IsAffineHom t := IsAffineHom.of_comp t C.ι
  have htr : t ≫ complementProjection i g hig hS = r := by
    dsimp only [complementProjection, r]
    rw [← Category.assoc, ht]
  let : IsAffineHom r := by rw [← htr]; infer_instance
  let : IsIso r := isIso_of_affine_proper_birational r hX hffh
  refine ⟨globalComplementSplitting
    i g hig hS (inv r ≫ t) ?_⟩
  rw [Category.assoc, htr, IsIso.inv_hom_id]

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension
