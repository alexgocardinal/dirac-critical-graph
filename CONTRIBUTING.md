# Contributing

Corrections, independent reproductions, and simplifications of the formal
proof are welcome.

For a proposed change:

1. identify the exact graph, theorem, or certificate affected;
2. run both Lean builds and the independent replay;
3. include the complete failing or passing output;
4. regenerate every affected checksum manifest; and
5. explain whether the axiom footprint changes.

Do not replace a failed theorem with `sorry`, `admit`, a user-declared axiom,
or an unchecked solver transcript. Discovery code may propose certificates,
but committed certificates must be checked by the provided proof-producing or
exact replay layer.

Security-sensitive reports, such as accidental credential publication, should
be sent privately to the repository owner rather than opened publicly.

