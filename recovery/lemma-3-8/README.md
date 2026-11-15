# Lemma 3.8 recovery checkpoint

The latest checkpoint is `verified_checkpoint.json` with `candidate.patch.gz`.
All nine new Lean modules compiled strictly; all thirty public theorem types,
axioms, source hashes, and manuscript correspondence were independently checked.
The full 707-export aggregate verification is running; exact-commit CI is pending.

Decompress the patch and apply it to a clean checkout of the `base_commit` in
that metadata file. The patch preserves the proof, ledger, correspondence,
and rendered documentation candidate. The older `source_checkpoint.json`
retains the initial uncompiled writing checkpoint for history.

This recovery branch does not replace the live main-branch execution evidence.
