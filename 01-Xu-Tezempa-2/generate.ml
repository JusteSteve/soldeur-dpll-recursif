
let generate_instance: unit -> unit = fun () ->
  print_endline "Entrez le nombre de sommets";
  let s = read_int() in 
  print_endline "Entrez le degré minimum des sommets";
  let  d = read_int() in 
  print_endline "Entrez la taille de la clique";
  let c = read_int() in
  (* afficher les valeurs de s, d et c*)
  Printf.printf "s = %d, d = %d, c = %d\n" s d c;;

let () = generate_instance ();;