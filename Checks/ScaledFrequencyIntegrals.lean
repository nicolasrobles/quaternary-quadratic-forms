import Lean
import QuaternaryQuadraticForms.FrequencyIntegralBounds
import QuaternaryQuadraticForms.LocalizedFrequencyIntegrals
import QuaternaryQuadraticForms.DeltaIntegralRegularity

run_cmd do
  let environment ← Lean.getEnv
  let names : List Lean.Name := [
    `QuaternaryQuadraticForms.DeltaIntegralBounds.scaledFrequency,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.uniform_singularIntegral_norm,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.small_modulus_zero_error,
    `QuaternaryQuadraticForms.source_localized_frequency_integrals,
    `QuaternaryQuadraticForms.deltaIntegral_contDiffOn_scale,
    `QuaternaryQuadraticForms.source_delta_integral_contDiffOn_scale]
  for name in names do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | _ => Lean.throwError "Expected a theorem declaration for {name}"
  let usedInputs : List Lean.Name := [
    `QuaternaryQuadraticForms.Trusted.heathBrown_delta_data,
    `QuaternaryQuadraticForms.Trusted.heathBrown_integral_reduction,
    `QuaternaryQuadraticForms.Trusted.heathBrown_oscillatory_bounds,
    `QuaternaryQuadraticForms.Trusted.heathBrown_singular_graph,
    `QuaternaryQuadraticForms.Trusted.heathBrown_weight_localization,
    `QuaternaryQuadraticForms.Trusted.heathBrown_zero_approximation,
    `QuaternaryQuadraticForms.Trusted.simon_graph_area]
  for name in usedInputs do
    match environment.find? name with
    | some (.axiomInfo _) => pure ()
    | _ => Lean.throwError "Expected a registered literature premise for {name}"
  let allInputs : List Lean.Name := [
    `QuaternaryQuadraticForms.Trusted.weil_simple_roots,
    `QuaternaryQuadraticForms.Trusted.katz_surface_spectral_data,
    `QuaternaryQuadraticForms.Trusted.lang_homogeneous_resultants,
    `QuaternaryQuadraticForms.Trusted.bertini_homogeneous_tangent,
    `QuaternaryQuadraticForms.Trusted.heathBrown_delta_data,
    `QuaternaryQuadraticForms.Trusted.simon_graph_area,
    `QuaternaryQuadraticForms.Trusted.heathBrown_weight_localization,
    `QuaternaryQuadraticForms.Trusted.heathBrown_singular_graph,
    `QuaternaryQuadraticForms.Trusted.heathBrown_zero_approximation,
    `QuaternaryQuadraticForms.Trusted.heathBrown_integral_reduction,
    `QuaternaryQuadraticForms.Trusted.heathBrown_oscillatory_bounds,
    `QuaternaryQuadraticForms.Trusted.poisson_four_dimensional]
  let _ ← environment.constants.foldM (init := ()) fun _ name info => do
    if (`QuaternaryQuadraticForms).isPrefixOf name then
      match info with
      | .axiomInfo _ =>
        unless allInputs.contains name do
          Lean.throwError "Unregistered project axiom: {name}"
      | _ => pure ()
    else
      pure ()
  pure ()

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.scaledFrequency
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.scaledFrequency

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.uniform_singularIntegral_norm
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.uniform_singularIntegral_norm

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.small_modulus_zero_error
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.small_modulus_zero_error

#check @QuaternaryQuadraticForms.source_localized_frequency_integrals
#print axioms QuaternaryQuadraticForms.source_localized_frequency_integrals

#check @QuaternaryQuadraticForms.deltaIntegral_contDiffOn_scale
#print axioms QuaternaryQuadraticForms.deltaIntegral_contDiffOn_scale

#check @QuaternaryQuadraticForms.source_delta_integral_contDiffOn_scale
#print axioms QuaternaryQuadraticForms.source_delta_integral_contDiffOn_scale

#check @QuaternaryQuadraticForms.Trusted.heathBrown_delta_data
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_delta_data

#check @QuaternaryQuadraticForms.Trusted.heathBrown_integral_reduction
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_integral_reduction

#check @QuaternaryQuadraticForms.Trusted.heathBrown_oscillatory_bounds
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_oscillatory_bounds

#check @QuaternaryQuadraticForms.Trusted.heathBrown_singular_graph
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_singular_graph

#check @QuaternaryQuadraticForms.Trusted.heathBrown_weight_localization
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_weight_localization

#check @QuaternaryQuadraticForms.Trusted.heathBrown_zero_approximation
#print axioms QuaternaryQuadraticForms.Trusted.heathBrown_zero_approximation

#check @QuaternaryQuadraticForms.Trusted.simon_graph_area
#print axioms QuaternaryQuadraticForms.Trusted.simon_graph_area
