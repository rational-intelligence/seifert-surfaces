# Verification commands

From the repository root after `lake exe cache get`:

```sh
python3 tools/verify.py
```

This is the single authoritative receiving verification command. It checks
source/certificate custody hashes, scans portable Lean tokens and recognized
serialized declaration payloads, builds the common `MainTheorems` entry, and
requires exactly **25 original heads plus one qualified support head** from
[RECEIVING_MANIFEST.json](RECEIVING_MANIFEST.json) to remain within
`propext`, `Classical.choice` and `Quot.sound`.

It verifies the pinned receiving-script, generic-codec and actual-fidelity
bundle hashes, executes the 15 literal/operative scripts with concurrency two,
and runs `actual-common/AuditActualCommon.lean` followed by its logical result
validator. The fixed 507-record result coverage includes 48 required
safe-operative equalities and the complete safe-to-partial reference boundary.
Failed logical fields, missing/extra record identities or unapproved proof
choices fail verification even when Lean exits zero. The command records the
actual receipt in `verification-reports/VERIFICATION_RUN.json`; a duplicate
internal 16-check batch is unnecessary.

```sh
python3 tools/verify.py --sources-only
lake env lean tools/Verify.lean
```

`--sources-only` checks custody, source tokens and recognized serialized
ConstantInfo payloads without running Lean. The decoded payload check rejects
axiom declarations and `sorryAx` references in recognized forms. Closed proof
expressions and certificate contents still require the normal Lean kernel;
the complete root audit supplies their transitive axiom boundary. The direct
`tools/Verify.lean` command is only the root audit, not the full receiving pass.

[VERIFICATION.json](../docs/VERIFICATION.json) records the final receiving
fidelity audits and their exact bounded receipts. The public command does not
rerun offline historical exporters. [BUILD_STATUS.md](../docs/BUILD_STATUS.md)
and [CONTEXTS.json](../docs/CONTEXTS.json) explain the common source environment
and archival provenance. Historical workspace paths in receipts are locators,
not runtime dependencies. No whole-archive or independent Mathlib-rebuild
certification is implied.
