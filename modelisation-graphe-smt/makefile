exec: generate.ml
	ocamlc generate.ml -o exec

run: exec
	./exec

stat:
	time z3 output.z3 > model.txt

clean:
	rm -f *.cmi *.cmo model.txt output.z3 exec