.data


.text
fact:
move $fp, $sp
sub $sp, $sp, 24
L14:
sw $ra, -4($sp)
sw $a0, 0($fp)
li $t0, 1
bge $a2, $t0, L11
j L12
L12:
move $v0, $a1
L10:
lw $ra, -4($sp)
j L13
L11:
lw $a0, 0($fp)
mul $a1, $a1, $a2
sub $a2, $a2, 1
jal fact
j L10
L13:
move $sp, $fp
addi $fp, $fp, 24
jr $ra

factorial:
move $fp, $sp
sub $sp, $sp, 24
L16:
sw $ra, -4($sp)
sw $a0, 0($fp)
move $a2, $a1
move $a0, $fp
li $a1, 1
jal fact
lw $ra, -4($sp)
j L15
L15:
move $sp, $fp
addi $fp, $fp, 24
jr $ra

main:
move $fp, $sp
sub $sp, $sp, 20
L18:
sw $ra, -4($sp)
sw $a0, 0($fp)
move $a0, $fp
li $a1, 7
jal factorial
lw $ra, -4($sp)
j L17
L17:
move $sp, $fp
addi $fp, $fp, 20
move $t0, $v0
li $v0, 1
move $a0, $t0
syscall
jr $ra

