; Exercice 1.1
; Cas s = 4, d = 3, c = 3

(declare-datatypes () ((S s4 s3 s2 s1)))
; l'ensemble des sommets du graphe est S = {s1, s2, s3, s4}

(declare-fun A (S S) Bool)
; le predicat A(si, sj) est vrai si l'arrête entre les sommets
; si et sj existe, faux sinon 

(assert (forall ((x S) (y S)) (=> (A x y) (distinct y x))))
; pas d'arête qui boucle

(assert (forall ((x S) (y S)) (=> (A x y) (A y x))))
; le graphe n'est pas dirigé

(assert (forall ((x S)) (exists ((x3 S)(x2 S)(x1 S))
                        (and (A x x3) (A x x2) (A x x1) (distinct x3 x2) (distinct x3 x1) (distinct x2 x1)))))
; le degré de chaque sommet est au moins 3

(assert (forall ((x3 S)(x2 S)(x1 S))
        (or (not (A x3 x2))(not (A x3 x1))(not (A x2 x1)))))
; il n’existe aucune clique de taille 3.

(check-sat)

(get-model)


