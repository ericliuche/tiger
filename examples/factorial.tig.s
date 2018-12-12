.data


.text
factorial:
move $fp, $sp
sub $sp, $sp, 20
L14:
sw $a0, 0($fp)
sw $a1, -8($fp)
sw $ra, -4($fp)
lw $t0, -8($fp)
li $t1, 1
ble $t0, $t1, L11
j L12
L12:
lw $a0, 0($fp)
lw $t0, -8($fp)
sub $a1, $t0, 1
jal factorial
lw $t0, -8($fp)
mul $v0, $t0, $v0
L10:
lw $ra, -4($fp)
j L13
L11:
li $v0, 1
j L10
L13:
move $sp, $fp
addi $fp, $fp, 20
jr $ra

main:
move $fp, $sp
sub $sp, $sp, 20
L16:
sw $a0, 0($fp)
sw $ra, -4($fp)
move $a0, $fp
li $a1, 7
jal factorial
lw $ra, -4($fp)
j L15
L15:
move $sp, $fp
addi $fp, $fp, 20
move $t0, $v0
li $v0, 1
move $a0, $t0
syscall
jr $ra

