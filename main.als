sig Veiculo { 
} {
    one this.~veiculos
    one this.~vVisitante
}

abstract sig Pessoa {  }

sig Visitante extends Pessoa {
    vVisitante: one Veiculo
} {
    one this.~visitantes
}

sig Morador extends Pessoa {
    veiculos: set Veiculo,
    visitantes: set Visitante
}

fact teste1 {
    one m: Morador, v: Visitante | v.vVisitante in m.veiculos and v in m.visitantes
}

fact maximoVeiculos {
    all m: Morador | #m.veiculos <= 3
}

pred show() {}
run show for 6