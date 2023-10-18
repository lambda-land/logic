# logic

This is package contains functions and typeclasses that are necessary to express inductive rule systems.

# Installation

Create a `cabal.project` file, then add
```yaml
packages: .

source-repository-package
    type: git
    location: https://github.com/lambda-land/logic
```

Then to your `[project name].cabal` file, add `logic` as a build depend,
```yaml
build-depends: base, ..., logic
```

