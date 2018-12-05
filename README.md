# Register Allocation

### Nick Flanders and Chenyang Eric Liu

Our register allocator attempts to coalesce and spill registers whenever
necessary. To simplify our implementation, we deviated from the specification
given in Appel's book by only maintaining an adjacency list rather than both
an adjacency list and an adjacency set. This slightly simplifies our
implementation at the cost of less efficient look ups.

Additionally, we included a final step in the register allocator which filters
out any unnecessary move instructions that are the result of moving between two
temps which were colored with the same register.

Due to a bug in our implementation of the coalescing and spilling stages of the
register allocator, certain programs which contain specific interactions
between coalesced and spilled registers cause the compiler to break as it is
unable to color a wrongly-coalesced node.