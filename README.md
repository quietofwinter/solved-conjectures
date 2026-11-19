# Solved conjectures

Proofs of mathematical conjectures. Each entry has a written proof, and the Lean column shows whether the proof has also been checked by machine in Lean 4. Each entry also says whether an earlier proof is known.

Maintained by Jason Benham.

## Results

| Result | Finding | Lean | Evidence |
|---|---|:---:|---|
| [Bala's supercongruence for OEIS A364175](a364175-bala-supercongruence/) | **First Lean-verified proof.** For every prime p ≥ 5 and all positive integers n and r, a(n·p^r) ≡ a(n·p^(r−1)) (mod p^(3r)), where a(n) = (6n)!·(2n/3)! / ((3n)!·(2n)!·(5n/3)!). Conjectured by Peter Bala in [OEIS A364175](https://oeis.org/A364175). An earlier written proof, not formalized, was given by R. A. Bajaj and A. Burns on August 1, 2026; the proof here was found independently. | ☑ | [Written proof](a364175-bala-supercongruence/A364175.pdf) · [Lean proof](a364175-bala-supercongruence/A364175.lean) · [Notes](a364175-bala-supercongruence/README.md) |
| [Integrality and Bala's supercongruence for OEIS A364172](a364172-bala-integrality/) | **Integrality proved; the supercongruence follows.** a(n) = (6n)!·(n/3)! / ((3n)!·(2n)!·(4n/3)!) from [OEIS A364172](https://oeis.org/A364172) is always an integer, and a(n·p^r) ≡ a(n·p^(r−1)) (mod p^(3r)) for every prime p ≥ 5 and all positive integers n and r, as conjectured by Peter Bala; the congruence also follows from integrality by a theorem of Bajaj and Burns (2026), and priority for integrality is provisional (no earlier proof found in a search on November 19, 2026). | ☑ | [Written proof](a364172-bala-integrality/A364172.pdf) · [Lean proof](a364172-bala-integrality/A364172.lean) · [Notes](a364172-bala-integrality/README.md) |

### What the Lean column means

| Mark | Meaning |
|:---:|---|
| ☑ | The full statement is proved in Lean 4. The file compiles with no `sorry` and uses only the standard axioms. |
| ◐ | Partly formalized. The entry lists what is still missing. |
| ☐ | Not formalized. |

## Scope

- These are unrefereed notes, not peer-reviewed publications.
- The proofs were developed with the assistance of Claude (Anthropic).
- Each entry names the earlier work it builds on and says which parts are new.
- Where someone else proved the result first, the entry says so and cites that proof. "First Lean-verified proof" means first as far as a search at the time of posting could find.
- A ☑ means Lean accepted the proof of the formal statement in that entry's Lean file. It does not by itself show that the formal statement matches the informal conjecture, so each entry says where its formal statement comes from.

## Checking a Lean proof

Every entry's notes give the exact Lean version and the commands used. For entries whose statements come from the [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) repository, the check looks like this:

```
git clone https://github.com/google-deepmind/formal-conjectures
cd formal-conjectures
git checkout <commit named in the entry>
lake exe cache get
lake env lean /path/to/the/entry.lean
```

The check passes if the last command prints no `error` lines. Warnings are harmless.

## Citing

Use the "Cite this repository" button on GitHub, which reads [CITATION.cff](CITATION.cff). Please also cite the sources named in the entry you use.

## Licence

Apache License 2.0. See [LICENSE](LICENSE). Lean files that build on other projects keep those projects' notices in their headers.
