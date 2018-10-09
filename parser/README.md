# Parser Assignment

#### Nicholas Flanders and Chenyang Liu


Our parser grammar does not generate any shift-reduce or reduce-reduce
conflicts. During the development of the grammar, we encountered several
aspects of the language that initially caused our parser to hit shift-reduce
conflicts.

### If-Then(-Else)

Our initial implementation of the if-then and if-then-else expressions caused
a shift-reduce conflict. To eliminate this conflict, we gave the if-then-else
rule a higher precedence than the if-then rule via token precedence. This means
that a string such as ```if a then if b then c else d``` will be unambiguously
parsed as ```if a then (if b then c else d)```.

### Declaration Sequences

Our initial implementation also produced shift-reduce conflicts for the parsing
of declaration sequences. Because consecutive function and type declarations
need to be grouped together into a single AST node, our first attempts at our
grammar led to ambiguous situations when it was unclear whether to reduce a
completed `fundecseq` or `typedecseq` or to shift and continue building the
current declaration sequence. Since we want the greedy approach which takes as
many consecutive declarations as possible, the default shift behavior would
have given us the desired outcome in this case. However, we got rid of the
conflict by changing our grammar to have three mutually recursive declaration
sequence types. This structure allows us to control which types of declaration
sequences must be reduced before continuing to read declarations of a specific
type which gave us the desired outcome without grammatic ambiguity.

### Efficient Sequence Parsing

There are several types of sequences in our grammar which we attempted to parse
in an efficient manner. Our general approach was to split each type of sequence
into a `seq` and a `nonemptyseq`. This allowed us to write a left-recursive
rule with separators for `nonemptyseq`. This is more memory-efficient in an
LR(1) parser compared to a right-recursive approach. However, if we built the
list in the order, then our semantic actions would have been less efficient
because they would have needed to append to the end of the list which is an
O(n) operation on linked lists. Therefore, we decided to build the list in
reverse and then reverse it a single time right before we construct the AST
node that it is part of.