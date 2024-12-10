open Printf
let generate_instance: unit -> unit = fun () ->
  print_endline "Entrez le nombre de sommets";
  let s = read_int() in 
  print_endline "Entrez le degré minimum des sommets";
  let  d = read_int() in 
  print_endline "Entrez la taille de la clique";
  let c = read_int() in
  (* afficher les valeurs de s, d et c*)
  printf "s = %d, d = %d, c = %d\n" s d c;

  let fic = open_out "output.z3" in 
  fprintf fic "(declare-datatypes () ((S ";
  for i = 1 to s do 
    fprintf fic " s%d" i
  done;
  fprintf fic ")))\n";

  fprintf fic "(declare-fun A (S S) Bool)\n";
  (*pas de boucle*)
  fprintf fic "(assert (forall ((x S) (y S)) (=> (A x y) (not (= y x)))))\n";
  (*le graphe n'est pas dirigé*)
  fprintf fic "(assert (forall ((x S) (y S)) (=> (A x y) (A y x))))\n";

  (*le degré de chaque sommet est au moins d*)
  fprintf fic "(assert (forall ((x S)) (exists (";
  for i = 1 to d do 
    fprintf fic "(x%d S) " i
  done;
  fprintf fic ") (and ";
  for i = 1 to d do 
    fprintf fic "(A x x%d) " i
  done;
  for i = 1 to d do 
    for j = i+1 to d do
      fprintf fic "(not (= x%d x%d)) " i j
    done
  done;
  fprintf fic "))))\n";

  (*il n’existe aucune clique de taille c*)
  fprintf fic "(assert (forall (";
  for i = 1 to c do 
    fprintf fic "(x%d S) " i
  done;
  fprintf fic ") (or ";
  for i = 1 to c do
    for j = i+1 to c do 
      fprintf fic "(not (A x%d x%d)) " i j
    done
  done;
  fprintf fic ")))\n";

  fprintf fic "(check-sat)\n";
  fprintf fic "(get-model)\n";
  close_out fic;;

  


let () = generate_instance ();;