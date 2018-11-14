# Intermediate Representation Translation

### Nick Flanders and Chenyang Eric Liu

Our Translate module exposes an interface to produce an IR tree from
a given abstract syntax expression or declaration. All of the translation
functions produce a Translate.exp which is internally recognizable as
an Ex value, an Nx statement, or a Cx control flow handler. Boolean
translations are converted to nested if-then(-else) statements, so our
translator handles these special cases to ensure that the nested control
flow operations produce relatively efficient IR code.

We define two exception types, IllegalProgramException and
OutermostLevelException, which are never raised in valid Tiger programs.

To resolve a variable reference across lexical scopes, we defined a
recursive function with an accumulator that consists of the IR tree
required to reach the frame pointer for the current lexical level.

Additionally, we build our list of Translate.frags in reverse order to
be more efficient and then reverse the list when it is retrieved after
translation. We also define a Translate interface function to reset the
translated frags to allow for multiple files to be compiled per invocation.

Finally, we define a few debugging utilities to easily print IR trees and
frags to standard out, although these are not called during translation.