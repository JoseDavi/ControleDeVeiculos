open util/boolean


sig Veiculo {
    validade: Bool,
    tempo: Int
}

// Fato que limita o número de moradores.
// Possui um problema onde, por algum motivo, o numero maximo de moradores não pode ser maior que 5.
fact maximoMoradoresCondomio {
    #(Morador) < 11
}

abstract sig Pessoa {}
    
sig Morador extends Pessoa {
    veiculos: set Veiculo,
    visitantes: set Visitante
}

sig Antes{
    entrando: lone Veiculo
}

sig Durante{
    entre: lone Veiculo
}

sig Depois{
    saindo: lone Veiculo
}

fact evitaStatus{
    no disj antes: Antes, durante: Durante| some antes.entrando & durante.entre
    no disj antes: Antes, depois: Depois| some antes.entrando & depois.saindo
    no disj depois: Depois, durante: Durante| some depois.saindo & durante.entre
}

fact MaxCatraca{
    #(Antes) = 1
    #(Durante) = 1
    #(Depois) = 1
}

sig Visitante extends Pessoa {
    veic: set Veiculo
}

// Esse fato determina que so pode existir veiculos caso exista um dono
fact veiculosComDono{
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
fact maximoVeiculos{
    all m: Morador |  #(m.veiculos + m.visitantes) < 4
    all v: Visitante | #v.veic = 1
}
// Fato que determina a Validade de um veiculo.
// Possui um problema onde, por algum motivo, o tempo maximo não pode ser maior que 5.
fact VerificaStatus {
    all v: Veiculo | ((v.tempo = 0) and (v.validade = False)) or ((v.tempo > 0) and (v.validade = True) and (v.tempo < 31))
}


pred show() {}
run show for 5 but 5 int

