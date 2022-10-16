# MiniF2F

**Note: This repository is a fork of the original OpenAI miniF2F repository [https://github.com/openai/miniF2F](https://github.com/openai/miniF2F), with additional data and many formal statement fixes.**

MiniF2F is a formal mathematics benchmark (translated across multiple formal systems) consisting of
exercise statements from olympiads (AMC, AIME, IMO) as well as high-school and undergraduate maths
classes.

The goal of the project is to provide a shared benchmark to evaluate and directly compare automated
theorem proving systems based on the formal systems targeted, initially **Lean**, **Isabelle**, and **Metamath**
(targeting also **Hol Light**).

The benchmark (released under permissive licenses (MIT for Metamath, Apache for Lean)) is a work in
progress and contributions are welcome and encouraged through pull requests.

## Citation

The initial version of the benchmark is described in detail in the following [pre-print](https://arxiv.org/abs/2109.00110):
```
@article{zheng2021minif2f,
  title={MiniF2F: a cross-system benchmark for formal Olympiad-level mathematics},
  author={Zheng, Kunhao and Han, Jesse Michael and Polu, Stanislas},
  journal={arXiv preprint arXiv:2109.00110},
  year={2021}
}
```

The original repo is [miniF2F](https://github.com/openai/miniF2F). It has then seen significant fixes and improvements, notably the addition of an informal statement and an informal proof for each problem. The curation of the informal component is described in the following [paper](https://openreview.net/forum?id=SMa9EAovKMC). To cite it:
```
@inproceedings{
  2210.12283,
  title={Draft, Sketch, and Prove: Guiding Formal Theorem Provers with Informal Proofs},
  author={Albert Q. Jiang and Sean Welleck and Jin Peng Zhou and Wenda Li and Jiacheng Liu and Mateja Jamnik and Timothée Lacroix and Yuhuai Wu and Guillaume Lample},
  booktitle={Submitted to The Eleventh International Conference on Learning Representations},
  year={2022},
  url={https://arxiv.org/abs/2210.12283}
}
```

We decided to start a separate repository, instead of submitting PRs, for better maintainence of the dataset.

## Statistics

|           | Test | Valid |
|:---------:|:----:|:-----:|
|   Lean    |  244 |  244  |
| Metamath  |  244 |  244  |
| Isabelle  |  244 |  244  |
| Hol Light |  165 |  165  |
| Informal  |  244 |  244  |


## Example problem statement (mathd_algebra_17)

#### Informal
Solve for $a$: $\sqrt{4+\sqrt{16+16a}}+ \sqrt{1+\sqrt{1+a}} = 6.$ Show that it is 8.

#### Lean
```lean
theorem mathd_algebra_17
  (a : ℝ)
  (h₀ : real.sqrt (4 + real.sqrt (16 + 16 * a)) + real.sqrt (1 + real.sqrt (1 + a)) = 6) :
  a = 8 :=
begin
  sorry
end
```

####  Isabelle
```isabelle
theorem mathd_algebra_17:
  fixes a :: real
  assumes "1 + a>0"
  assumes "sqrt (4 + sqrt (16 + 16 * a)) 
    + sqrt (1 + sqrt (1 + a)) = 6" 
  shows "a = 8"
  sorry
```

####  HOL Light
```ml
let mathd-algebra-17 = `!a. sqrt (&4 + sqrt (&16 + &16 * a)) + sqrt (&1 + sqrt (&1 + a)) = &6 /\ &0 <= (&1 + a) ==> a = &8`;;
```

####  Metamath
```mm
$(
  @{
    mathd-algebra-17.0 @e |- ( ph -> A e. RR ) $@
    mathd-algebra-17.1 @e |- ( ph -> ( ( sqrt ` ( 4 + ( sqrt ` ( ; 1 6 + ( ; 1 6 x. A ) ) ) ) ) + ( sqrt ` ( 1 + ( sqrt ` ( 1 + A ) ) ) ) ) = 6 ) $@
    mathd-algebra-17 @p |- ( ph -> A = 8 ) @=
      ? @.
  @}
$)
```

## Structure

Each problem is represented by a unique name and a file for each of the formal systems we target.
Each file consists at minima in the problem statement and optionally one or more example proofs
associated with it. The benchmark is divided in two splits:

- `valid`: validation set that can be used while designing automated theorem proving systems
  (early-stopping, reinforcement learning, data-augmentation, curriculum design, ...).
- `test`: held-out test set reserved for final evaluation.

Naming conventions are still a work in progress. Olympiads problems are generally named after their
competition year and problem number (eg. `imo-1990-p3` or `aime-1983-p2`). Problems coming from a
particular dataset (eg the [MATH](https://arxiv.org/abs/2103.03874) dataset) are named to ease their
retrieval (eg. `mathd-algebra-125`). Other problems are prefixed by a category hint and a unique
name in the style of Metamath naming conventions (eg. `induction-11div10tonmn1ton`).

Each exercise file complies to the following system-specific conventions.

### Lean

To install the project make sure you have [elan](https://github.com/leanprover/elan) installed,
then in the directory where you want the project installed run:

```
git clone https://github.com/openai/miniF2F
cd miniF2F
leanpkg configure
leanproject get-mathlib-cache
leanproject build
```

Since having one file per statement causes slowness in Lean parsing stage, all Lean statements are
exceptionally aggregated in two files (`valid.lean` and `test.lean`). These files contain a list of
the problem statements defined as `theorem`s. Optionally, proofs for these statements are provided
as well as potential lemmas to support the ground-truth proof.

No `theorem` should appear that do not correspond to a problem statement; use `lemma` instead.

Please use `lean/scripts/lint_style.py` to check all the statements pass the linter. You can also
make use of `lean/scripts/simple_formatter.sh` to enforce a few basic formatting rules.

The `lean` folder is released under the Apache License (so that it is aligned with Lean's mathlib
license).

### Metamath

Each file contains the problem statement with the same name as the problem unique name. The
statement is commented (using Metamath convention) if provided without proof.

The `metamath` folder is released under the MIT License.

### HOL Light

Each file contains the problem statement defined as a HOL Light term
whose name must match the file name.

The `hollight` folder is released under the FreeBSD License.

### Isabelle

Each file contains the problem statement defined as a theorem
whose name must match the file name, optionally with a proof for it as well as the necessary imports.

The `isabelle` folder is released under the Apache License.

### Informal

Each file contains the problem statement and the proof written in natural mathematical language. The data come from the following sources:
- The [MATH](https://github.com/hendrycks/math) dataset.
- The [AOPS](https://artofproblemsolving.com/) website.
- Manual annotation by Albert Qiaochu Jiang, Timothée Lacroix, Guillaume Lample, Sean Welleck, Jiacheng Liu, and Marie-Anne Lachaux.

## Code of Conduct and Contributions

MiniF2F is meant to serve as a shared and useful resource for the machine learning community working
on formal mathematics. 

There is no obligation tied with the use and reporting of a result based on miniF2F. But if you're
using it and discovering new proofs (manually or automatically) please contribute them back to the
benchmark.

All contributions, such as new statements for later versions, addition of missing statements for
existing versions, bug fixes, additional proofs are all welcome.

## Versioning

A version of miniF2F is defined by a frozen set of statements. The goal for each version is to get
full coverage on all formal systems for that version even if that might not be the case when the
version is frozen.

When reporting a result based on miniF2F please always specify the version you used. The current
version is `v2`, frozen as of October 2022, including 488 statements (fully translated to Lean, Isabelle, and Metamath but still WIP in other formal systems).

Each version will live in its own branch to allow later additions of translated statements or fixes
to existing statements as needed. The `main` branch remains reserved for active development and
should not be used when reporting results.

### Active version

- Version `v2`
- Freeze date: October 2022
- Branch: [v2](https://github.com/albertqjiang/miniF2F/tree/v2)

### Previous versions

- Version: `v1`
- Freeze date: August 2021
- Branch: [v1](https://github.com/openai/miniF2F/tree/v1)
