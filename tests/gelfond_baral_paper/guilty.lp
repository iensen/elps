sorts
#person = {john, peter}.
predicates

guilty(#person).
presumed_innocent(#person).
cleared(#person).

rules

guilty(john) | guilty(peter).
presumed_innocent(X):- not K$guilty(X).
cleared(X):- not M$guilty(X).
-cleared(X):- not cleared(X).
-presumed_innocent(X):- not presumed_innocent(X).

