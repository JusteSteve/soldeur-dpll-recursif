(declare-datatypes () ((S s4 s3 s2 s1)))
; l'ensemble des sommets du graphe est S = {s1, s2, s3, s4}

(declare-fun A (S S) Bool)
; le predicat A(si, sj) est vrai si l'arrête entre les sommets
; si et sj existe, faux sinon 

(assert (forall ((x S) (y S)) (=> (A x y) (not (= y x)))))
; pas d'arête qui boucle

(assert (forall ((x S) (y S)) (=> (A x y) (A y x))))
; le graphe n'est pas dirigé

(assert (forall ((x S)) (exists ((x2 S) (x1 S))
                        (and (A x x2) (A x x1) (not (= x2 x1))))))
; le degré de chaque sommet est au moins 2

(assert (forall ((x3 S)(x2 S)(x1 S))
        (or (not (A x3 x2))(not (A x3 x1))(not (A x2 x1)))))
; il n’existe aucune clique de taille 3.
; que les sommets x1 , x2 , x3 soient distincts car , si
; On remarque qu ’il n’est pas necessaire de demander
; un meme sommet est pris deux fois , l’absence d’aretes qui bouclent
; implique que la formule "(or (not (A x3 x2))..." est verifiee.

(check-sat)

(get-model)
; si la conjonction des assertions ci-dessus a un modele , on recupere
; une interpretation de A qui les satisfait toutes. Cette interpretation
; de A decrit un graphe a 4 sommets de degre au moins 2 sans 3- cliques