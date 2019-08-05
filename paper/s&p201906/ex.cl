proc main (uint64 in, uint64 N) =
{ true && in < 2@64 * N }
subc b t in N;
sbcs dontcare mask 0@uint64 0@uint64 b;
assert true && or [mask = 0@64, mask = 0xffffffffffffffff@64];
and r0@uint64 mask in;
not nmask@uint64 mask;
and r1@uint64 nmask t;
or r@uint64 r0 r1;
assert true && or [r = in, r = in - N];
{ true && r < N }
