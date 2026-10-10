# Verification commands

From the repository root, after `lake exe cache get`:

```sh
python3 tools/verify.py
```

This checks the committed custody hashes, scans portable source entries for
placeholders outside comments/strings, builds `MainTheorems` and
`ConformalOriginals`, and requires the exact documented root axiom output to
stay within the classical base. It does not verify the historical archive.

Direct Lean audit commands are:

```sh
lake env lean tools/Verify.lean
lake env lean tools/VerifyConformal.lean
```

Historical native contexts and source rebuild gaps are documented in
`docs/BUILD_STATUS.md` and `docs/CONTEXTS.json`. Their absolute old paths are
archival provenance, not runtime requirements of these commands.
