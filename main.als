open util/boolean

sig Veiculo {
    validade: Bool,
    tempo: Int
}

abstract sig Pessoa {}
    
sig Morador extends Pessoa {
    veiculos: set Veiculo,
    visitantes: set Visitante
}

sig Visitante extends Pessoa {
    veic: set Veiculo
}

// Esse fato determina que so pode existir veiculos caso exista um dono
fact veiculosComDono {
    all v: Visitante| one v.~visitantes
    all vei: Veiculo | one vei.~veiculos or one vei.~veic
}

// fato que evita que dois moradores ou visitantes diferentes possuam o mesmo veiculo
fact evitaVeiculosRepetidosMorador {
    no disj m1, m2: Morador | some m1.veiculos & m2.veiculos 
    no disj v1, v2: Visitante | some v1.veic & v2.veic
}

// fato que será discutido posteriormente, evita que dois moradores possuam o mesmo visitante
fact evitaVisitantesRepetidosMorador {
    no disj m1, m2: Morador | some m1.visitantes & m2.visitantes
}

//Fato que evita que o visitante seja dono do mesmo veiculo que o proprietario
fact evitaVeiculosRepetidosVisitanteMorador {
    no disj  m1: Morador, v1: Visitante | some m1.veiculos & v1.veic 
}

// fato que determina que o morador possui mo maximo 3 veiculos e o visitante 1 veiculo
fact maximoVeiculos {
    all m: Morador |  #(m.veiculos + m.visitantes) < 4
    all v: Visitante | #v.veic = 1
}

// Fato que determina a quantidade de dias maximos que um veiculo pode passar na garagem
fact ValidadeMaxima {
    all v: Veiculo, m: Morador, vi: Visitante| ((v.~veiculos = m) and (v.tempo <= 30)) or ((v.~veic = vi) and (v.tempo <= 1))
}

// Fato que determina a Validade de um veiculo.
fact VerificaStatus {
    all v: Veiculo | ((v.tempo = 0) and (v.validade = False)) or ((v.tempo > 0) and (v.validade = True))
}

pred show() {}
run show for 2