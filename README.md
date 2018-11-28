# Live Variable Analysis

### Nick Flanders and Chenyang Eric Liu

Our MakeGraph module exposes functions to construct a control flow graph from
a given list of assembly instructions. This graph is then used to construct an
interference graph from the information contained within the CFG. We first
calculate the live-in and live-out sets through an algorithm which iteratively
updates the sets until we find a fixed point. Then, we look through the
live-out sets of our nodes and insert interference edges as appropriate.

Since we used many set operations in this stage of the compiler, we added a
Set type to temps. This enabled us to easily find unions and intersections
while creating our interference graph.