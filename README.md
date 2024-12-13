# The Gobra Book: Formally Verifying Go Programs with Gobra

<img align="right" width="100" height="100" src="./theme/favicon.svg">

This repository contains the source of the *Gobra Book*, an online learning resource for [Gobra](https://github.com/viperproject/gobra), a verifier for the Go programming language.

🚧 Work in progress - we are in the process of writing the core chapters 🚧

You can access the latest version at <https://viperproject.github.io/gobra-book/>

Have you found an error? Please file an [issue](https://github.com/viperproject/gobra-book/issues/new/choose).

For contribution and building information please refer to [CONTRIBUTING.md](./CONTRIBUTING.md).

## Licenses
The contents of the Gobra Book in `src/` and `quizzes/` are licensed under the [Mozilla Public License v2.0](./licenses/LICENSE-MOZILLA).


We are grateful to the following open source projects:

- <https://github.com/rust-lang/mdBook> ([Mozilla Public License v2.0](./licenses/LICENSE-MOZILLA)) which we use to generate the website, based on the files `theme/*`.

- <https://github.com/cognitive-engineering-lab/mdbook-quiz/> ([Apache License](./licenses/LICENSE-APACHE), [MIT License](./licenses/LICENSE-MIT)) which is used to integrate interactive quizzes.

- <https://github.com/rust-lang/book> ([Apache License](./licenses/LICENSE-APACHE), [MIT License](./licenses/LICENSE-MIT)) which was used as the base for the CI/CD actions and the script `ci/spellcheck.sh`

- <https://github.com/ajaxorg/ace>  ([License](./licenses/LICENSE-ACE)) which provides a code editor and golang support via `mode-golang.js`
