# Instructions for this verification project

- Freeze manuscript/quadratic_character_sums_github.tex at the SHA-256 in
  certification/source.json. The filename differs from the supplied v35;
  the content must remain identical unless the authors explicitly revise it.
- Trust exact cited literature inputs used by the proofs. Do not reprove the
  references. Register exact statements and locators before introducing a Lean
  premise, and check all manuscript-specific hypotheses and specializations.
- Do not turn an internal lemma, estimate, definition, or missing deduction
  into an external premise. The claims refuted in Remark 4.1 and the
  introduction are excluded comparisons, not trusted inputs.
- Use official Lean and reputable libraries. Keep Lean, mathlib, and the
  transitive dependency revisions pinned.
- A numbered result is Certified only after every clause is kernel checked
  and its statement and dependencies have passed source correspondence review.
  Do not infer certification from a successful build or from a helper theorem.
- Preserve the distinction between numbered results, supporting exports,
  literature premises, and auxiliary/supplementary obligations.
- Use the actual arithmetic and geometric objects. Generic numerical algebra
  can be a useful helper but does not certify a theorem about character sums.
- No proof placeholders, unregistered axioms, native evaluation, or unchecked
  shortcuts. The verifier inspects actual theorem types and dependencies.
- Update the live status ledger, readable inventory, and execution checkpoint
  together when a claimed scope changes. Link checked exports to their Lean
  files and record the exact checked commit and successful run when available.
- Report Complete, Partial, Active, and Pending counts for numbered results.
  Do not reopen already checked work without a concrete reason.
