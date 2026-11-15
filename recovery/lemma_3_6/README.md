# Lemma 3.6 recovery checkpoint

This branch preserves verified supporting work during the ongoing Lemma 3.6 proof. The full lemma remains Pending. The certified main branch stays at the completed Lemma 3.5 milestone.

The three source snapshots contain six public theorems: the uniform divisor bound, uniform logarithmic-power bound, and four exact prime-support counting statements. Each passed strict Lean compilation and actual type/axiom inspection. Every inspected theorem uses only Classical.choice, Quot.sound, and propext. No literature premise is added.

The source snapshots retain the original Lean bytes and use the .lean.txt suffix to identify recovery copies. Their original module paths and SHA-256 values are recorded in checkpoint.json. The two inspection logs preserve the actual printed types and dependencies.

The full mixed-sum estimate, its source correspondence review, and the full repository verification are still outstanding at this checkpoint. No completion of Lemma 3.6 is claimed here.
