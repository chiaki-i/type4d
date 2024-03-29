# type4d

The repository provides the [Agda](https://agda.readthedocs.io/en/v2.6.2/getting-started/what-is-agda.html) implementation of the paper ["Type system for four delimited control operators"](https://dl.acm.org/doi/10.1145/3564719.3568691) presented in [GPCE 2022 - 21st International Conference on Generative Programming: Concepts & Experiences](https://2022.splashcon.org/home/gpce-2022#event-overview).

## File description

The implementation is included in `code/` folder.

Tested on Agda 2.6.2.2

| Section | File name | Description |
| ------- | --------- | ----------- |
| Section 3 and 4 | 4D.agda   | type system and CPS interpreter for four control operators (4D) |
| Section 5.1 | shift-DF.agda | type system and CPS interpreter for shift/reset in 1CPS (DF) without trails nor meta continuations |
| Section 5.1 | shift-DF2.agda | type system and CPS interpreter for shift/reset in 2CPS (DF2) without trails, with meta continuations (function) |
| Section 5.1 | shift-4Dfun.agda         | type system and CPS interpreter for shift/reset in 2CPS (4Dfun) with trails and meta continuations (function) |
| Section 5.1 | shift-DF-DF2-eq.agda     | translation between DF and DF2 |
| Section 5.1 | shift-DF2-4Dfun-eq.agda  | translation between DF2 and 4Dfun |
| Section 5.2 | control-CP.agda          | type system and CPS interpreter for control/prompt in 1CPS (CP) with trails, without meta continuations |
| Section 5.2 | control-4Dfun.agda       | type system and CPS interpreter for control/prompt in 2CPS (4Dfun) with trails and meta continuations (function) |
| Section 5.2 | control-CP-4Dfun.agda    | translation between CP and 4Dfun |
| Section 5.3 | shift0-MB.agda           | type system and CPS interpreter for shift0/reset0 (MB) |
| Section 5.3 | shift0-4Ddash.agda       | type system and CPS interpreter for shift0/reset0 in 2CPS (4D) without trails, with meta continuations (pair) |
| Section 5.3 | shift0-4D.agda           | type system and CPS interpreter for shift0/reset0 (4D) with trails and meta continuations (pair) |
| Section 5.3 | shift0-MB-4Ddash-eq.agda | translation between MB and 4Ddash |
| Section 5.3 | shift0-4Ddash-4D-eq.agda | translation between 4Ddash and 4D |
