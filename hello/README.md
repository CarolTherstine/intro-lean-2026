# Hello!

Welcome to the "hello" library.  Here is a summary of the main project files:

* [lean-toolchain](lean-toolchain): Toolchain file, specifying the Lean toolchain version to use.
* [lakefile.toml](lakefile.toml): The "lakefile", specifying how the project is to be built.
* [Hello.lean](Hello.lean): Your library entry point.
* [Hello](Hello): Your library sources.
* [HelloTest](HelloTest): Tests.
* [.gitignore](.gitignore): Things that should not be committed to repo.

## Building and testing

```bash
lake build
lake test
```
