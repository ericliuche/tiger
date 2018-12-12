.data


.text
factorial:
sw $fp -4($sp)
move $fp, $sp
sub $sp, $sp, 32
L14:
sw $a0, 0($fp)
sw $a1, -12($fp)
sw $ra, -8($fp)
lw $t0, -12($fp)
li $t1, 1
ble $t0, $t1, L11
j L12
L12:
lw $a0, 0($fp)
lw $t0, -12($fp)
sub $a1, $t0, 1
jal factorial
lw $t0, -12($fp)
mul $v0, $t0, $v0
L10:
lw $ra, -8($fp)
j L13
L11:
li $v0, 1
j L10
L13:
move $sp, $fp
lw $fp -4($fp)
jr $ra

main:
sw $fp -4($sp)
move $fp, $sp
sub $sp, $sp, 28
L16:
sw $a0, 0($fp)
sw $ra, -8($fp)
move $a0, $fp
li $a1, 7
jal factorial
lw $ra, -8($fp)
j L15
L15:
move $sp, $fp
lw $fp -4($fp)
move $t0, $v0
li $v0, 1
move $a0, $t0
syscall
jr $ra

