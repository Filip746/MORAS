@R0
D = M

@R5
M = D

@R1
D = M

@R5
D = D - M

//napravi promjenu na D, ako je R1 - R5 < 0 (tj ako je R1 < R5)
//i postavi R5 na trenutni max

@Promjena1
D;JLT

@R1
D = M

@R5
M = D

(Pro1)

@R2
D = M

@R5
D = D - M

@Promjena2
D;JLT

@R2
D = M

@R5
M = D

(Pro2)
@R3
D = M

@R5
D = D - M

@Promjena3
D;JLT

@R3
D = M

@R5
M = D

(Pro3)
@R4
D = M

@R5
D = D - M

@Promjena4
D;JLT

@R4
D = M

@R5
M = D

(Pro4)

(END)
@END
0;JMP