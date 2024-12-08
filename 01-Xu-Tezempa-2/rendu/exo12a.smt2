; Exercice 1.2
; Cas s = 5, d = 3, c = 3

(declare-datatypes () ((S s5 s4 s3 s2 s1)))
; l'ensemble des sommets du graphe est S = {s1, s2, s3, s4, s5}

(declare-fun A (S S) Bool)

(assert (forall ((x S) (y S)) (=> (A x y) (not (= y x)))))

(assert (forall ((x S) (y S)) (=> (A x y) (A y x))))

(assert (forall ((x S)) (exists ((x3 S)(x2 S)(x1 S))
                        (and (A x x3) (A x x2) (A x x1) (not (= x3 x2)) (not (= x3 x1)) (not (= x2 x1))))))

(assert (forall ((x3 S)(x2 S)(x1 S)) 
        (or (not (A x3 x2))(not (A x3 x1))(not (A x2 x1)))))

(check-sat)

(get-model)