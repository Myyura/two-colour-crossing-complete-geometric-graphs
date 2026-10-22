# Exact finite diagnostics

Run from the repository root with Python 3.10 or later:

```bash
python3 computations/run_checks.py
```

No solver, NumPy, credentials, network access or external model service is
used. The command reconstructs each result and compares it with
`expected-results.json`, including the checked program hashes. To intentionally
record a revised implementation, use `--record computations/expected-results.json`
and review the resulting changes.

| Program | Scope |
|---|---|
| `appendix_completion.py` | All 16,384 global-colour-swap representatives of a convex K6, with the two source edges constrained equal or different. Cramer's rule reconstructs crossings. Both full optima are 3; the non-source contribution differs. |
| `core_combinatorics.py` | All six orders of three source vertices with q=2, W=3, D=5. Exact parabola geometry checks affine palette fields, dummy cancellation, local crossing counts and inter-bundle amplification. These small parameters do not satisfy the forcing regime. |
| `program_geometry.py` | Two reduced exact double-chain configurations, including actual general-position insertion of two copies of every prototype, all required class exclusions, and selected/nonselected response tables. This checks geometric identities, not the large-parameter reduction's optimum. |
| `parameter_checks.py` | Integer/rational coefficient inequalities and the conservative error budget at five source sizes. It is not an all-n proof. |

The core and geometry programs are retained from independent local checks of
the proof. The six-point check was made portable and the parameter check uses
the formally established conservative local bound 2SW^4. The public Lean
artifact supplies the universal mathematical proofs. No timing or success of
these finite diagnostics is used as a substitute for them.
