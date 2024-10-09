# The Gobra Book: Formally Verifying Go Programs with Gobra

Work in progress.

## Contributing
The chapters are written as markdown files and located in the `src` directory.
This project uses [mdbook](https://rust-lang.github.io/mdBook/) so please refer to its documentation.

### Local Building

This assumes you have [Rust's package manager cargo installed](https://doc.rust-lang.org/cargo/getting-started/installation.html).

Install
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

