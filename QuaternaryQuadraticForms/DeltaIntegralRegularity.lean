import QuaternaryQuadraticForms.PoissonAnalytic
import Mathlib.Analysis.Convolution

/-! # Smooth dependence on the scale of the actual oscillatory integral -/

noncomputable section
namespace QuaternaryQuadraticForms

open MeasureTheory Set
open scoped ContDiff Convolution

/-- At fixed frequency the oscillatory integral is smooth for every positive scale.
The integrand has a common compact support in its Euclidean integration variable. -/
theorem deltaIntegral_contDiffOn_scale (F : RealVector4 → ℝ) (hF : ContDiff ℝ ∞ F)
    (w : RealVector4 → ℂ) (hw : IsSmoothWeight w) (v : RealVector4) :
    ContDiffOn ℝ ∞ (fun r => deltaIntegral F w r v) (Ioi 0) := by
  let g := fun (r : ℝ) (x : RealVector4) => w (-x) * (heathBrownDeltaKernel (r,F (-x)) : ℂ) *
    Complex.exp (2*(Real.pi:ℂ)*Complex.I*((-inner ℝ v (-x)/r : ℝ) : ℂ))
  let s : Set (ℝ × RealVector4) := Ioi 0 ×ˢ univ
  have hn : ContDiff ℝ ∞ (fun z : ℝ × RealVector4 => -z.2) := contDiff_snd.neg
  have hk : ContDiffOn ℝ ∞ (fun z : ℝ × RealVector4 => heathBrownDeltaKernel (z.1,F (-z.2))) s :=
    heathBrownDeltaKernel_properties.1.comp (contDiff_fst.prodMk (hF.comp hn)).contDiffOn
      (fun _ hz => hz.1)
  have hp : ContDiffOn ℝ ∞ (fun z : ℝ × RealVector4 => -inner ℝ v (-z.2)/z.1) s :=
    (contDiff_const.inner ℝ hn).neg.contDiffOn.div contDiff_fst.contDiffOn (fun _ hz => ne_of_gt hz.1)
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) s :=
    ((hw.1.comp hn).contDiffOn.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hk)).mul
      (Complex.contDiff_exp.comp_contDiffOn
        (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hp)))
  obtain ⟨R,hR⟩ := hw.2.isBounded.exists_norm_le
  have he := contDiffOn_convolution_right_with_param_comp (μ := (volume : Measure RealVector4))
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)
    (v := fun _ : ℝ => (0 : RealVector4)) (f := fun _ => (1 : ℝ)) (g := g)
    (n := ⊤) contDiffOn_const isOpen_Ioi (isCompact_closedBall (0 : RealVector4) R)
    (fun p x _ hx => by
      have h : w (-x) = 0 := by
        by_contra h
        exact hx (by simpa [Metric.mem_closedBall] using hR _ (subset_tsupport _ h))
      simp [g,h]) (by exact locallyIntegrable_const _) hg
  simpa [convolution_def, g, deltaIntegral] using he

/-- The regularity assertion in the setup for (5.5), on the original quadratic
form for every smooth weight, including all the localized pieces of Lemma 2.2. -/
theorem source_delta_integral_contDiffOn_scale (A : Matrix (Fin 4) (Fin 4) ℤ)
    (w : RealVector4 → ℂ) (hw : IsSmoothWeight w) (v : RealVector4) :
    ContDiffOn ℝ ∞ (fun r => deltaIntegral (realQuadraticValue (A.map (Int.castRingHom ℝ))) w r v)
      (Ioi 0) :=
  deltaIntegral_contDiffOn_scale _ (realQuadraticValue_contDiff _) w hw v

end QuaternaryQuadraticForms
