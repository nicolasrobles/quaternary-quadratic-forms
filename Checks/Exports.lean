import Lean
import QuaternaryQuadraticForms

run_cmd do
  let environment ← Lean.getEnv
  match environment.find? `QuaternaryQuadraticForms.weighted_ray_sum with
  | some (.thmInfo _) => pure ()
  | _ => Lean.throwError "Expected a theorem declaration for weighted_ray_sum"

#check @QuaternaryQuadraticForms.weighted_ray_sum
#print axioms QuaternaryQuadraticForms.weighted_ray_sum

