# Introduction to Lean 2026

See the example project [hello](hello).

To add your project to this repo, fork the repo and, run the following at the top-level dir, replacing `<NAME>` by the name of your project:

```bash
lake +leanprover-community/mathlib4:lean-toolchain new <NAME> math
```

This command will create a project tree similar to that of [hello](hello) under directory `<NAME>`.

You might need to edit the created `<NAME>/lakefile.toml`, for example, to customize the Lean options, add further dependencies, or add a test driver.
