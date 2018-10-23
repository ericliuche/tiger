# Static Semantics

### Nick Flanders and Chenyang Eric Liu

Our type-checker uses a lattice such that `BREAK` is the bottom type and `TOP`
is the top type. We use the helper functions `join` and `isSubtype` to aid
in checking the correctness of types.

Our `transExp` function takes both a variable environment and a type
environment as well as an `inLoop` flag. Based on the value of `inLoop`,
`transExp` returns a functions which will either allow or disallow any
`break` statements it encounters while recursively checking types.
Whenever we enter a loop, we call `transExp(venv, tenv, true) exp` instead of
`trexp(exp)` in order to switch into the appropriate context. Likewise,
whenever we call a function or enter a context where break is not allowed,
we call `transExp(venv, tenv, false) exp` to switch out of the loop context
if we are in one.

We wrap our `ErrorMsg.error` logic in an `error` function which sets a
`legalAst` flag to `false` whenever an error is encountered.

Additionally, we re-use our symbol table implementation in a couple of
locations other than our variable and type environments, such as when we check
if function names are unique and when we check for cyclical type definitions.