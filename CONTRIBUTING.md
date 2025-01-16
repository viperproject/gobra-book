# Contributing

The chapters are written as markdown files and located in the `src` directory.
This project is based on [mdbook](https://rust-lang.github.io/mdBook/) so please refer to its documentation if something is not described here.

As an overview we mention the important files:

- `src/SUMMARY.md` defines the index of the book, new chapters must be referenced here

- `book.toml` is the mdbook configuration file

- `editor.js` configures the code editor

- `theme/` for the styling and interactivity (especially `theme/book.js`)

## Local Building
This assumes you have [Rust's package manager cargo installed](https://doc.rust-lang.org/cargo/getting-started/installation.html).

Install `mdbook` with
``` sh
cargo install mdbook
```

For the interactive quizzes we need the `mdbook-quiz` preprocessor
``` sh
cargo install mdbook-quiz --locked --version 0.3.10
```

Now you can build the book locally

``` sh
mdbook build # generates the files in the book directory
mdbook serve # Serve the site and rebuild on changes
```


## Source Code
Source code can be included in either in markdown code blocks
````markdown
``` go
package main
// @ requires
func foo() {

}
```
````
or included
```markdown
{{#include examples/dutchflag.gobra}}
```

The source files used in this project have the extensions `.go` or `.gobra`. `.go` files consist of compilable Go files with specifications written in comments: `// @ ` signals a single line of specification, whereas comments within delimiters`/*@` and `@*/` signal multi-line specifications.


### Code Block Attributes
> [!WARNING]
> This behavior is likely to change

Source blocks can be tagged with attributes like `editable` or `runnable`:
````markdown
``` go,editable,runnable
...
```
````
For `runnable` code

### Style
Before proposing extensions to the book, please make sure that your examples satisfy the following conditions:
1. It is syntactically correct
2. It was formatted with [go fmt](https://go.dev/blog/gofmt)
3. It is written in idiomatic Go, e.g., it adheres to standard naming conventions

### Hiding boilerplate
Lines starting with `~` are hidden and can be toggled with a button. Currently the `hide-boring` attribute must be given to the block.
````markdown
```go,hide-boring
~package tutorial
~
```
````

## Quizzes
Quizzes can be inserted with the `quiz` directive:
``` markdown
{{#quiz ../quizzes/rust-variables.toml}}
```
They are defined in the toml format.
As an example multiple choice question:
```` toml
[[questions]]
type = "MultipleChoice"
prompt.prompt = """
**Program 1:**
```go
// @ ensures res >= 0
func square(x int) (res int) {
	return x * x
}
r := square(a)
// @ assert r == a*a
What is the verification result of **Program 1**?
"""
prompt.distractors = [
	"Verification Succeeds. `square` has no side effects and always returns `a*a`. Hence the assertion passes.",
	"Timeout. This is a hard problem and can not be solved in reasonable time.",
]
answer.answer = "Verification Fails. `r==a*a` cannot be established from the postcondition."
context = "Verification is modular and Gobra does not peek into function definitions."
```
````
If there are multiple correct answers, `answer.answer` is a list.
For a question of type `ShortAnswer` the user must type in the answer.

For the full description of the schema please refer to <https://github.com/cognitive-engineering-lab/mdbook-quiz>.

## Spellchecking
Please spell check locally for spelling errors before pushing.
We provide a simple spellchecker in our CI to detect obvious typos, but it does not find grammatical mistakes.
All markdown files in `src` are  assumed to be written in and spellchecked against `LANG=en_US.UTF-8` using `aspell`.
You may run the spellchecker using one of the following commands:
```sh
# check for errors and fix them interactively
bash ci/spellcheck.sh check
# List all errors (may report false positives)
bash ci/spellcheck.sh list

Custom words can be added to [dictionary.txt](ci/dictionary.txt) (it must remain sorted).
Note that code blocks are ignored, so you are responsible to check for typos in comments and identifiers.

