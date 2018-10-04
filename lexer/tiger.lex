type svalue = Tokens.svalue
type pos = int
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token


(* Error handling *)
val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1, p2) = ErrorMsg.error p1

(* Increments the line count and tracks the current lexer position *)
fun handleNewline(yypos) = (lineNum := !lineNum + 1; linePos := yypos :: !linePos)


(* The depth of nested comments that the lexer is currently at *)
val commentDepth = ref 0

(* Handles the start of a new potentially nested comment *)
fun startComment() =
    commentDepth := !commentDepth + 1

(* Handles the end of a potentially nested comment *)
fun endComment(yypos) =
    commentDepth := !commentDepth - 1    

(* Tracks if the lexer is currently within a string literal *)
val inString = ref false

(* Tracks the part of a string literal that has already been lexed *)
val curString = ref ""

(* Controls whether the lexer is currently within a string literal *)
fun beginString() = inString := true

(* Ends the current string and produces the token from the lexed text *)
fun createString(yypos) =
    let val token = Tokens.STRING(!curString, yypos - size(!curString) - 1, yypos + 1) in
        inString := false;
        curString := "";
        token
    end

(* Append the given chars to the string currently being parsed *)
fun appendChars(chars) =
    curString := !curString ^ chars

(* Converts the given ASCII escape sequence to its string representation *)
fun decodeAscii(escapeString) =
    case Int.fromString(substring(escapeString, 1, 3)) of
        SOME integer => Char.toString(chr(integer))
      | None => ""


(* Handles the EOF and errors if it is within a comment *)
fun eof() =
    let val pos = hd(!linePos) in
        if !commentDepth > 0 then
            (ErrorMsg.error pos "Unexpected end of file inside of a comment")
        else if !inString then
            (ErrorMsg.error pos "Unexpected end of file inside string literal")
        else
            ();
        Tokens.EOF(pos, pos)
    end


%%

%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));

digit=[0-9];
letter=[a-zA-Z];
ws=[ \t];

nonprintable=[ \n\t\f];
ctrlChar=[A-Z@^_]|"\\"|"["|"]";
asciiCode="\\"(([01]{digit}{digit})|(2[0-4]{digit})|(25[0-5]));
ctrlSeq="\\^"{ctrlChar};

%s COMMENT STRING STRINGESCAPE ERROR;

%%


<INITIAL>\n    => (handleNewline(yypos); continue());
<INITIAL>{ws}  => (continue());

<INITIAL>"type"      => (Tokens.TYPE(yypos, yypos + 4));
<INITIAL>"var"       => (Tokens.VAR(yypos, yypos + 3));
<INITIAL>"function"  => (Tokens.FUNCTION(yypos, yypos + 8));
<INITIAL>"break"     => (Tokens.BREAK(yypos, yypos + 5));
<INITIAL>"of"        => (Tokens.OF(yypos, yypos + 2));
<INITIAL>"end"       => (Tokens.END(yypos, yypos + 3));
<INITIAL>"in"        => (Tokens.IN(yypos, yypos + 2));
<INITIAL>"nil"       => (Tokens.NIL(yypos, yypos + 3));
<INITIAL>"let"       => (Tokens.LET(yypos, yypos + 3));
<INITIAL>"do"        => (Tokens.DO(yypos, yypos + 2));
<INITIAL>"to"        => (Tokens.TO(yypos, yypos + 2));
<INITIAL>"for"       => (Tokens.FOR(yypos, yypos + 3));
<INITIAL>"while"     => (Tokens.WHILE(yypos, yypos + 5));
<INITIAL>"else"      => (Tokens.ELSE(yypos, yypos + 4));
<INITIAL>"then"      => (Tokens.THEN(yypos, yypos + 4));
<INITIAL>"if"        => (Tokens.IF(yypos, yypos + 2));
<INITIAL>"array"     => (Tokens.ARRAY(yypos, yypos + 8));

<INITIAL>":="        => (Tokens.ASSIGN(yypos, yypos + 2));
<INITIAL>"|"         => (Tokens.OR(yypos, yypos + 1));
<INITIAL>"&"         => (Tokens.AND(yypos, yypos + 3));
<INITIAL>">="        => (Tokens.GE(yypos, yypos + 2));
<INITIAL>">"         => (Tokens.GT(yypos, yypos + 1));
<INITIAL>"<="        => (Tokens.LE(yypos, yypos + 2));
<INITIAL>"<"         => (Tokens.LT(yypos, yypos + 1));
<INITIAL>"<>"        => (Tokens.NEQ(yypos, yypos + 2));
<INITIAL>"="         => (Tokens.EQ(yypos, yypos + 1));
<INITIAL>"/"         => (Tokens.DIVIDE(yypos, yypos + 1));
<INITIAL>"*"         => (Tokens.TIMES(yypos, yypos + 1));
<INITIAL>"-"         => (Tokens.MINUS(yypos, yypos + 1));
<INITIAL>"+"         => (Tokens.PLUS(yypos, yypos + 1));
<INITIAL>"."         => (Tokens.DOT(yypos, yypos + 1));
<INITIAL>"}"         => (Tokens.RBRACE(yypos, yypos + 1));
<INITIAL>"{"         => (Tokens.LBRACE(yypos, yypos + 1));
<INITIAL>"]"         => (Tokens.RBRACK(yypos, yypos + 1));
<INITIAL>"["         => (Tokens.LBRACK(yypos, yypos + 1));
<INITIAL>")"         => (Tokens.RPAREN(yypos, yypos + 1));
<INITIAL>"("         => (Tokens.LPAREN(yypos, yypos + 1));
<INITIAL>":"         => (Tokens.COLON(yypos, yypos + 1));
<INITIAL>";"         => (Tokens.SEMICOLON(yypos, yypos + 1));
<INITIAL>","         => (Tokens.COMMA(yypos, yypos + 1));

<INITIAL>"/*"        => (YYBEGIN COMMENT; startComment(); continue());
<INITIAL>"*/"        => (ErrorMsg.error yypos ("Unexpected end of comment"); YYBEGIN ERROR; continue());
<COMMENT>"/*"        => (startComment(); continue());
<COMMENT>"*/"        => (case !commentDepth of
                            0 => (ErrorMsg.error yypos ("illegal end of comment"); YYBEGIN ERROR; continue())
                        |   1 => (endComment(); YYBEGIN INITIAL; continue())
                        |   _ => (endComment(); continue()));
<COMMENT>"\n"        => (handleNewline(yypos); continue());                        

<COMMENT>.           => (continue());


<INITIAL>"\""         => (YYBEGIN STRING; beginString(); continue());
<STRING>([^\"\\])*    => (appendChars(yytext); continue());
<STRING>{asciiCode}   => (appendChars(decodeAscii(yytext)); continue());
<STRING>"\\n"         => (appendChars("\n"); continue());
<STRING>"\\t"         => (appendChars("\t"); continue());
<STRING>"\\\\"        => (appendChars("\\"); continue());
<STRING>"\\\""        => (appendChars("\""); continue());
<STRING>{ctrlSeq}     => (appendChars(yytext); continue());
<STRING>"\\"{nonprintable} => (YYBEGIN STRINGESCAPE; continue());
<STRING>"\""          => (YYBEGIN INITIAL; createString(yypos));

<STRING>.             => (ErrorMsg.error yypos ("illegal charater in string: " ^ yytext); YYBEGIN ERROR; continue());
<INITIAL>"\"\""       => (Tokens.STRING("", yypos, yypos + 2));

<STRINGESCAPE>"\n"    => (handleNewline(yypos); continue());
<STRINGESCAPE>{ws}+   => (continue());
<STRINGESCAPE>"\\"    => (YYBEGIN STRING; continue());
<STRINGESCAPE>.       => (ErrorMsg.error yypos ("illegal charater in string escape sequence: " ^ yytext);
                          YYBEGIN ERROR;
                          continue());

<INITIAL>{digit}+  => (case Int.fromString(yytext) of
                          SOME integer => Tokens.INT(integer, yypos, yypos + size(yytext))
                        | NONE => ((ErrorMsg.error yypos ("Illegal integer " ^ yytext)); YYBEGIN ERROR; continue()));

<INITIAL>{letter}({letter}|{digit}|_)*  => (Tokens.ID(yytext, yypos, yypos + size(yytext)));


<ERROR>.    => (continue());
<ERROR>\n   => (handleNewline(yypos); continue());
<INITIAL>.  => (ErrorMsg.error yypos ("illegal character " ^ yytext); YYBEGIN ERROR; continue());
