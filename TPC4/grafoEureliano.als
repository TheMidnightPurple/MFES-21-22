// Modelo circuito eureliano
sig Nodo {
	var adjacentes : set Nodo,
	var caminho : set Nodo,
	var nodoInicial : one Nodo,
	var nodoAtual : one Nodo
}



fact {
	//um nodo não pode ser adjacente a sí próprio
	all n : Nodo | n not in n.adjacentes
	//se nodo A é adjacente ao nodo B, então nodo B é adjacente ao nodo A 
	all n1 : Nodo, n2 : Nodo | n1 in n2.adjacentes implies n2 in n1.adjacentes
	//um nodo não pode estar isolado
	all n : Nodo | some n.adjacentes	
}


fact Init {
	//no início não há nenhum caminho
	no caminho
	//no início, o nodo Atual será o nodo Inicial
	nodoInicial = nodoAtual		
}


pred stutter {
	adjacentes' = adjacentes
	caminho' = caminho
	nodoInicial' = nodoInicial
	nodoAtual' = nodoAtual
}


pred advance [n : Nodo] {
	//guard 
	some n.adjacentes
	n = Nodo.nodoAtual	

	//effect
	one n1 : Nodo | all n2 : Nodo - n - n1 | n1 in n.adjacentes and (
				     n.caminho' = n.caminho + n1 and 
				     n.adjacentes' = n.adjacentes - n1 and 
				     n1.adjacentes' = n1.adjacentes - n and
				     n2.adjacentes' = n2.adjacentes and
				     Nodo.nodoAtual' = n1)
	
	//frame conditions
	nodoInicial' = nodoInicial
	all n1 : Nodo - n | n1.caminho' = n1.caminho
	
}


fact final {
	eventually (no adjacentes and nodoInicial = nodoAtual)	
}

fact events {
	always (
		 stutter or
		 some n : Nodo | advance[n]
	 )
}

run Exemplo {
	all disj n, n1 : Nodo | n1 in n.adjacentes
}for exactly 5 Nodo, 1..20 steps
