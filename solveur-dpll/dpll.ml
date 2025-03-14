(* MP1 2024/2025 - dpll.ml *)

open List

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien y ajouter.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   afficher le résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)


(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai 
*)
let simplifie l clauses =
  let filter cl = 
    if (mem l cl) then None (* supprimer clause contenant un littéral donné *)
    else 
      let filtre_supprimer_negation p = 
        if p <> (-l) then Some(p) else None (* supprimer la négation du littéral donné *)
      in Some(filter_map filtre_supprimer_negation cl) 
  in filter_map filter clauses
      

(* 
solveur_split : int list list -> int list -> int list option
 exemple d'utilisation de `simplifie' 
*)
(* 
cette fonction ne doit pas être modifiée, sauf si vous changez 
le type de la fonction simplifie 
*)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)
(*let () = print_modele (solveur_split ([[1; 2; 3]; [2;4]; [3]; [-1; 4]]) [])*)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int
    - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
    - sinon, lève une exception `Failure "pas de littéral pur"' 
*)
let pur clauses =
  (* Extraire tous les littéraux dans un seul ensemble *)
  let lits = flatten clauses in
  (* Filtrer les littéraux pures : ceux qui n'ont pas leur opposé dans lits *)
  let is_pur l = not (mem (-l) lits) in
  try
    (* Trouver le premier littéral pur *)
    let lit_pur = find is_pur lits in
    lit_pur
  with Not_found -> raise (Failure "pas de littéral pur")


(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, lève une exception `Not_found' 
*)
let unitaire clauses =
  (* si la clause contient un littéral unitaire le retourne *)
  let rec aux clauses =  (* Correction ici : on travaille sur la liste des clauses *)
    match clauses with
    | [] -> raise Not_found  (* Aucune clause unitaire trouvée *)
    | [lit] :: _ -> lit      (* Si une clause unitaire est trouvée, retourne le littéral *)
    | _ :: rest -> aux rest  (* Continue avec les autres clauses *)
  in
  try aux clauses with Not_found -> raise Not_found


(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  match clauses with
  | [] -> Some interpretation (* si l'ensemble des clauses est vide alors la formule est satisfiable *)
  | _ when mem [] clauses  -> None (* clause vide insatisfiable *)
  | _  -> 
    try (* simplifier littéral unitaire si il y'en a *) 
      let lit_unit = unitaire clauses in 
      solveur_dpll_rec (simplifie lit_unit clauses) (lit_unit::interpretation)
    with Not_found -> 

      try (* simplifier littéral pur si il y'en a *)
        let lit_pur = pur clauses in
        solveur_dpll_rec (simplifie lit_pur clauses) (lit_pur::interpretation)
      with Failure _ ->

        let lit = hd (hd clauses) in (* sinon choisir un littéral *)
        let branche = solveur_dpll_rec (simplifie lit clauses) (lit::interpretation) in 

        match branche with 
          | None -> solveur_dpll_rec (simplifie (-lit) clauses) ((-lit)::interpretation) (* si branche insatisfiable, on prend la négation *)
          | _ -> branche (* si branche satisfiable on la renvoie *)

(* tests *)

(* ----------------------------------------------------------- *)

(* let () = print_modele (solveur_dpll_rec systeme []) *)
 (*let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])

