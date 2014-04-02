sorts
#s = {a}.

predicates
p(#s).

rules

:-   K$ p(a).
:-   not K$ p(a).
:-   K$ -p(a).
:-   not K$ -p(a).
:-   M$ p(a).
:-   not M$ p(a).
:-   M$ -p(a).
:-   not M$ -p(a).
