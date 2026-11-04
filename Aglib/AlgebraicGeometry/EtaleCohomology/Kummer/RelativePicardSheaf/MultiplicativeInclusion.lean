/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.MultiplicativeComparison

/-! The original Gm and Picard chart maps preserve the original Kummer inclusion. -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe e

attribute [local instance] hasSheafifyLarge

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]

/-- The ORIGINAL root inclusion commutes with the actual etale Gm coefficient isomorphism. -/
theorem gmEtalePullbackIso_inclusion (n : ℕ) (hn : 0 < n)
    (hi : IsUnit (n : Γ(X, ⊤))) :
    (inverseImage f).map (inclusion X n) ≫ (gmEtalePullbackIso f).hom =
      (rootsPullbackIso f n hn hi).hom ≫ inclusion Y n := by
  have hc := (sequencePullbackHom f n).comm₁₂
  change torsorAdjunctionCoefficient f (q := rootsUnit f n) ≫ inclusion Y n =
    (inverseImage f).map (inclusion X n) ≫
      torsorAdjunctionCoefficient f (q := gmUnit f) at hc
  rw [rootsUnit_adjoint f n hn hi, gmUnit_adjoint_etale] at hc
  exact hc.symm

variable [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]

/-- Evaluate the actual coefficient-composition equality before applying Picard classification. -/
theorem gmEtaleCohomology_inclusion (n : ℕ) (hn : 0 < n)
    (hi : IsUnit (n : Γ(X, ⊤))) (q : ℕ)
    (c : Sheaf.H.{e} ((inverseImage f).obj (mu X n)) q) :
    Sheaf.H.map (gmEtalePullbackIso f).hom q
      (Sheaf.H.map ((inverseImage f).map (inclusion X n)) q c) =
    Sheaf.H.map (inclusion Y n) q
      (Sheaf.H.map (rootsPullbackIso f n hn hi).hom q c) :=
  (Sheaf.H.map_comp_apply ((inverseImage f).map (inclusion X n))
    (gmEtalePullbackIso f).hom c).symm.trans
      ((congrArg (fun k => Sheaf.H.map k q c) (gmEtalePullbackIso_inclusion f n hn hi)).trans
        (Sheaf.H.map_comp_apply (rootsPullbackIso f n hn hi).hom (inclusion Y n) c))

/-- The original Picard inverse preserves the actual inclusion square on every etale test. -/
theorem gmEtalePicard_inclusion (n : ℕ) (hn : 0 < n)
    (hi : IsUnit (n : Γ(X, ⊤)))
    (c : Sheaf.H.{e} ((inverseImage f).obj (mu X n)) 1) :
    (Picard.picardCohomologyEquiv Y).symm
      (Sheaf.H.map (gmEtalePullbackIso f).hom 1
        (Sheaf.H.map ((inverseImage f).map (inclusion X n)) 1 c)) =
      rootsPicardMap Y n (Sheaf.H.map (rootsPullbackIso f n hn hi).hom 1 c) :=
  congrArg (Picard.picardCohomologyEquiv Y).symm (gmEtaleCohomology_inclusion f n hn hi 1 c)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Picard

universe e
open Scheme.RelativePicard Scheme.EtaleCohomology.Kummer
open Scheme.Modules.Invertible Scheme.Modules.Invertible.PullbackTensor.Local
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}} (p : X ⟶ S)
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom p))]

/-- The original chart Gm equivalence preserves the actual root inclusion. -/
theorem fibreProductGmPicardEquiv_inclusion (U : S.Etale)
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))
    (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom p)).obj (mu X n)) 1) :
    fibreProductGmPicardEquiv p U
      (Sheaf.H.map ((inverseImage (pullback.snd U.hom p)).map (inclusion X n)) 1 c) =
        fibreProductRootsPicardMap p n hn hi U c :=
  congrArg (pullbackClass (pullbackSymmetry p U.hom).hom)
    (gmEtalePicard_inclusion (pullback.snd U.hom p) n hn hi c)

end AlgebraicGeometry.Scheme.EtaleCohomology.Picard
