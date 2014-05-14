sorts
#s1 = {a,b,c}.
#s2 = {a,c}.

predicates
p(#s1).
q(#s2).
r(#s2).

rules
p(a)|p(b).
q(X):- not M$p(X).
r(X):- M$p(X).
