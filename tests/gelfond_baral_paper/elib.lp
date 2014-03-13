sorts
#student = {mike,mary}.

predicates

eligible(#student).
highGPA(#student).
fairGPA(#student).
minority(#student).
interview(#student).

rules
eligible(X):- highGPA(X).
eligible(X):- minority(X), fairGPA(X).
-eligible(X):- -fairGPA(X), -highGPA(X).
interview(X):- not K$ eligible(X), not K$ -eligible(X).

% data
fairGPA(mike) | highGPA(mike).
highGPA(mary).


