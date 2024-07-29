-- NUMERICAL SEMIGROUP FREE RESOLUTION FUNCTIONS

-- A numerical semigroup is a subset of the nonnegative integers that contains
-- 0, is closed under addition, and has finite complement. A numerical semigroup
-- can be written in terms of a generating set: S = <n_1, ..., n_k>. We assign
-- each generator a variable: n_i <-> x_i. We then define a function phi from the
-- polynomial ring K[x_1,...,x_k] to the polynomial ring K[t] (k some base field)
-- by phi(x_i) = t^(n_i). The toric ideal of S is I_S = ker(phi), and the
-- semigroup algebra is k[S] = im(phi). 

-- takes in the generators of a semigroup as a list L, prints the first maxLen
-- terms of the infinite free resolution of the base field k over the semigroup
-- algebra k[S]
generalInfinite := (L, maxLen) -> (
    k = (length L) - 1;
    S = QQ[y,x_1..x_(k), Degrees => L];
    T = QQ[t];
    F = map(T, S, apply(L, n -> t^n));
    I = ker F;
    R = S/I;
    M = coker vars R;
    res (minimalPresentation M, LengthLimit => maxLen))


-- An extra-generalized arithmetic numerical semigroup is a numerical semigroup
-- of the form S = <m, mh + d, mh + 2d, ..., mh + kd>. The following functions
-- take m, h, d, and k as inputs and print various information about free
-- resolutions related to the generated EGANS.

-- prints the finite free resolution of K[S] as a k[y,x_1,...,x_k]-module
EGANSFinite := (m, h, d, k) -> (
L = {m};
for i from 1 to k do (L = append(L, m*h + i*d));
S = QQ[y,x_1..x_k, Degrees => L];
T = QQ[t];
F = map(T, S, apply(L, n -> t^n));
I = ker F;
res module I)

-- prints the first maxLen terms of the infinite free resolution of the base field
-- k over the semigroup algebra k[S]
EGANSInfinite := (m, h, d, k, maxLen) -> (
L = {m};
for i from 1 to k do (L = append(L, m*h + i*d));
S = QQ[x_1..x_(k+1), Degrees => L];
T = QQ[t];
F = map(T, S, apply(L, n -> t^n));
I = ker F;
R = S/I;
M = coker vars R;
res (M, LengthLimit => maxLen))

-- prints the first maxLen columns of the Betti table of the infinite free
-- resolution of k over k[S]
EGANSInfiniteBettiTable := (m, h, d, k, maxLen) -> (
L = {m};
for i from 1 to k do (L = append(L, m*h + i*d));
S = QQ[x_1..x_(k+1), Degrees => L];
T = QQ[t];
F = map(T, S, apply(L, n -> t^n));
I = ker F;
R = S/I;
M = coker vars R;
minimalBetti (M, LengthLimit => maxLen))

-- This code returns a list of graded degrees of the first homDegree 
-- modules of the infinite free resolution of k over k[S].
EGANSInfiniteDegreeList := (m, h, d, k, homDegree) -> (
L = {m};
for i from 1 to k do (L = append(L, m*h + i*d));
S = QQ[x_1..x_(k+1), Degrees => L];
T = QQ[t];
F = map(T, S, apply(L, n -> t^n));
I = ker F;
R = S/I;
M = coker vars R;
f = res (M, LengthLimit => homDegree);
degreeList = flatten degrees f_homDegree)


