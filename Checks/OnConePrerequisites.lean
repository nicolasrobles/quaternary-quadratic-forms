import Lean
import QuaternaryQuadraticForms.DualConeCounting
import QuaternaryQuadraticForms.ConeFrequencyAbel

run_cmd do
  let environment ← Lean.getEnv
  let names : List Lean.Name := [
    `QuaternaryQuadraticForms.source_dual_cone_count,
    `QuaternaryQuadraticForms.cone_modulus_abel_bound,
    `QuaternaryQuadraticForms.coneIntegralWeight_derivative,
    `QuaternaryQuadraticForms.DeltaIntegralBounds.onCone_modulus_sum]
  for name in names do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | _ => Lean.throwError "Expected a theorem declaration for {name}"
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

#check @QuaternaryQuadraticForms.source_dual_cone_count
#print axioms QuaternaryQuadraticForms.source_dual_cone_count

#check @QuaternaryQuadraticForms.cone_modulus_abel_bound
#print axioms QuaternaryQuadraticForms.cone_modulus_abel_bound

#check @QuaternaryQuadraticForms.coneIntegralWeight_derivative
#print axioms QuaternaryQuadraticForms.coneIntegralWeight_derivative

#check @QuaternaryQuadraticForms.DeltaIntegralBounds.onCone_modulus_sum
#print axioms QuaternaryQuadraticForms.DeltaIntegralBounds.onCone_modulus_sum
