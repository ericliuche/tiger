PROCEDURE L11 
L17:
li $t1, 1
ble $t0, $t1, L14
j L15
L15:
lw $a0, $fp
sub $a1, $t0, 1
jal factorial
mul $v0, $t0, $v0
L13:
j L16
L14:
li $v0, 1
j L13
L16:
END L11



PROCEDURE L10 
L19:
move $a0, $fp
li $a1, 7
jal factorial
j L18
L18:
END L10
